open System.Numerics
open System.Security.Cryptography

let bigint (x:int) = bigint(x) // Oddities  with F#

let KEYSIZE = 64
let HLEN = 32 // Length in octets of hash output, in this case SHA-256
let SLEN = 16 // Length in octets of salt for EMSA


let modexp a b n = //from Rosetta Code, calculates a^b (mod n)
    let mulMod x y n = snd (BigInteger.DivRem(x * y, n))
    let rec loop a b c =
        if b = 0I then c else
            let (bd, br) = BigInteger.DivRem(b, 2I)
            loop (mulMod a a n) bd (if br = 0I then c else (mulMod c a n))
    loop a b 1I


let modulo n m = // Because F#'s modulo doesn't handle negatives properly (-367 % 3120 = 2753, not -367!)
    let mod' = n % m
    if sign mod' >= 0 then mod'
    else abs m + mod'

let rec gcd (x: bigint) (y: bigint) = // Greatest common divisor, recursive Euclidean algorithm
    if y = 0I then x
    else gcd y (x % y)

let random n = // Generate a random number n bytes long
    let mutable bytes : byte array = Array.zeroCreate n
    (new System.Random()).NextBytes(bytes)
    abs (new BigInteger (bytes))

let rec ext_gcd (x:bigint) (y:bigint) = // Solve for the equation ax + by = gcd(a,b). When a nd b are coprime (i.e
                                        // gcd(a,b) = 1, x is the modular multiplicative inverse of a modulo b. 
                                        // This is crucial for calculating the private exponent. Implements the 
                                        // Extended Euclidean algorithm.
    if y = 0I then
        (1I,0I)
    else
        let q = x/y
        let r = x - y*q
        let (s,t) = ext_gcd y r
        (t, s-q*t)


let coprime n = // Find a coprime of n (gcd(n, x) = 1)
    let mutable test = random KEYSIZE
    while ((gcd n test) <> 1I) do 
        test <- random KEYSIZE
    test

let rec prime () = // Find a (probable) prime
    let x = random KEYSIZE
    let y = coprime x
    if modexp y (x-1I) x = 1I then x
    else prime ()


let modmultinv (e:bigint) (n:bigint) = // Find the modular multiplicative inverse of e mod n. That is, e * x = 1 (mod n)
    let (x,_) = ext_gcd e n
    modulo x n

let keys () = 
    let p = prime() // Pick an arbitrary large prime
    let mutable q = prime() // Pick another one
    while p = q do q <- prime() // Make sure they're different
    let n = p*q // This number is used as the modulus for the keys
    let phi = (p-1I)*(q-1I) // Euler's totient function. I am not very sure why this is used, but it is, so there
    let e = 65537I // 65537 is prime and therefore coprime to everything, and suitably large
    let d = modmultinv e phi
    ((n,e), (n,d))

let keylen ((n: bigint), (exp:bigint)) = 
    Array.length(n.ToByteArray())*8 + Array.length(exp.ToByteArray())*8


let (pubkey, privkey) = keys()

let str2os (x: string) = [for c in x -> (byte) c]

let os2str (octets: byte list) =  [for c in octets -> char c] |> List.fold(fun acc c -> acc + (string c)) ""

let i2osp (x:bigint) len = // Convert a nonnegative integer to an octet string of a certain length (see RFC 3447)
    if x >= 256I**len then raise (System.ArgumentException("x must be < 256^len"))
    let mutable divrem = BigInteger.DivRem(x, 256I);
    let mutable octets : byte list = []
    while (fst divrem) <> 0I do
        octets <- List.append octets [(snd divrem) |> byte]
        divrem <- BigInteger.DivRem((fst divrem), 256I)

    octets <- List.append octets [(snd divrem) |> byte]
    divrem <- BigInteger.DivRem((fst divrem), 256I)
    while List.length octets < len do octets <- List.append octets [0uy]
    List.rev octets


let rec os2ip (octets : byte list) (n: bigint) = // Convert an octet string to a nonnegative integer.
    match octets with
    | [] -> n
    | X::XS ->
    let acc = n + (X |> int |> bigint) * (256I ** (List.length XS))
    os2ip XS acc


let rsaep m (n, e) = // RSA Encryption Primitive    
    if m < 0I || m > (n-1I) then raise (System.ArgumentException("m out of range"))
    modexp m e n 

let rsasp = rsaep // RSA Signing Primitive. Identical to RSAEP
   
let rsadp c (n, d) = // RSA Decryption Primitive
    if  c < 0I || c > (n-1I) then raise (System.ArgumentException("c out of range"))
    modexp c d n

let rsavp = rsadp // RSA Verification Primitive. Identical to RSADP

let hash (bytes: byte list) = Array.toList ((SHA256.Create()).ComputeHash((List.toArray bytes)));

let mgf seed len = //Mask Generation Function, see Section B.2.1 of RFC 3447
    if len > 2I**32 * (HLEN|>bigint) then raise (System.ArgumentException("mask too long"))
    let lenfloat = len |> float;
    let hlenfloat = HLEN |> float;
    let final = ceil((lenfloat/hlenfloat)-1.0) |> int
    let x = [for c in [0..final] ->  hash (List.concat [seed; i2osp (c|>bigint) 4])]
    let T = List.concat x
    T |> Seq.take (len|>int) |> Seq.toList



let rsaes_oaep_encrypt ((n,e) as key) (M: byte list) L = // RSA OAEP Encryption. See Section 7.1 of RFC 3447. M and L should be provided as octet strings 
    let k = List.length (i2osp n (KEYSIZE*2)) // Length of modulus in octets
    if (M.Length) > (k - 2*HLEN - 2) then raise (System.ArgumentException("message too long"))
    let lHash = hash L
    let PS = List.init (k - (M.Length) - 2 * HLEN - 2) (fun x -> 0uy)
    let DB = List.concat [lHash; PS; [1uy]; M]
    let seed = i2osp (random HLEN) HLEN
    let dbMask = mgf seed ((k-HLEN-1) |> bigint)
    let maskedDB = List.map2 (fun x y -> x ^^^ y) DB dbMask
    let seedMask = mgf maskedDB (HLEN|>bigint)
    let maskedSeed = List.map2 (fun x y -> x ^^^ y) seed seedMask
    let EM = List.concat [[0uy]; maskedSeed; maskedDB]
    let m = os2ip EM 0I
    let c = rsaep m key
    i2osp c k

let rsaes_oaep_decrypt ((n,d) as key) C L = // RSA OAEP Decryption. See Section 7.1 of RFC 3447. C and L should be provided as octet strings
    let k = List.length (i2osp n (KEYSIZE*2))
    if (List.length C) <> k then raise (System.ArgumentException("decryption error"))
    let c = os2ip C 0I;
    let m = rsadp c key
    let EM = i2osp m k
    let lHash = hash L
    let maskedSeed = EM |> Seq.skip 1 |> Seq.take HLEN |> Seq.toList
    let maskedDB = EM |> Seq.skip (1+HLEN) |> Seq.take (k-HLEN-1) |> Seq.toList
    let seedMask = mgf maskedDB (HLEN |> bigint)
    let seed = List.map2 (fun x y -> x^^^y) maskedSeed seedMask
    let dbMask = mgf seed ((k-HLEN-1) |> bigint)
    let DB = List.map2 (fun x y -> x^^^y) maskedDB dbMask
    let lHash' = DB |> Seq.take HLEN |> Seq.toList
    if lHash' <> lHash then raise (System.ArgumentException("decryption error"))
    DB |> Seq.skip HLEN |> Seq.skipWhile (fun x -> x <> 1uy) |> Seq.skip 1 |> Seq.takeWhile (fun x -> true) |> Seq.toList

let salt len = i2osp (random len) len

let emsa_pss_encode M emBits (salt: byte list) = //EMSA Encoding. See Section 9.1.1 of RFC 3447
    let emLen = emBits/8
    let mHash = hash M
    if emLen < HLEN + salt.Length + 2 then raise (System.ArgumentException("encoding error"))
    let M' = List.concat [List.init 8 (fun x -> 0uy); mHash; salt]
    let H = hash M'
    let PS = List.init (emLen - salt.Length - HLEN - 2) (fun x -> 0uy)
    let DB = List.concat [PS; [1uy]; salt]
    let dbMask = mgf H ((bigint emLen) - (bigint HLEN) - 1I)
    let maskedDB = List.map2 (fun x y -> x ^^^ y) DB dbMask
    List.concat [maskedDB; H;[byte 0xbc]]

let emsa_pss_verify (M: byte list) (EM: byte list) emBits = // EMSA Verification. See Section 9.1.2 of RFC 3447
    let emLen = emBits/8
    let mHash = hash M
    if emLen < HLEN + SLEN + 2 then raise (System.ArgumentException("inconsistent"))
    if EM.[EM.Length-1] <> (byte 0xbc) then raise (System.ArgumentException("inconsistent"))
    let maskedDB = EM |> Seq.take (emLen - HLEN - 1) |> Seq.toList
    let H = EM |> Seq.skip (emLen - HLEN - 1) |> Seq.take HLEN |> Seq.toList
    let dbMask = mgf H ((bigint emLen) - (bigint HLEN) - 1I)
    let DB = List.map2 (fun x y -> x ^^^ y) maskedDB dbMask
    let test = DB |> Seq.take (emLen - HLEN - SLEN - 1) |> Seq.toList
    if test.[test.Length-1] <> 1uy then raise (System.ArgumentException("inconsistent"))
    let zeroes = test |> Seq.take (test.Length-1) |> Seq.toList
    if List.exists (fun x -> x <> 0uy) zeroes then raise (System.ArgumentException("inconsistent"))
    let salt = DB |> Seq.skip (DB.Length - SLEN) |> Seq.take SLEN |> Seq.toList
    let M' = List.concat [List.init 8 (fun x -> 0uy); mHash; salt]
    let H' = hash M'
    if H <> H' then raise (System.ArgumentException("inconsistent"))
    true

let rsassa_pss_sign ((n, d) as key) M = // RSA Signing, see Section 8.1.1 of RFC 3447
    let EM = emsa_pss_encode M ((List.length (i2osp n (KEYSIZE*2)))*8 - 1) (salt SLEN)
    let m = os2ip EM 0I
    let s = rsasp m key
    i2osp s (KEYSIZE*2)

let rsassa_pss_verify ((n,e) as key) M S = // RSA Verification, see Section 8.1.2 of RFC 3447
    let s = os2ip S 0I
    let m = rsavp s key
    let emLen = ((List.length (i2osp n (KEYSIZE*2))*8) - 1)/8
    let em = i2osp m emLen
    emsa_pss_verify M em ((List.length (i2osp n (KEYSIZE*2)))*8 - 1)
