open System.Numerics

let bigint (x:int) = bigint(x)

let KEYSIZE = 64


let modexp a b n = //from Rosetta Code
    let mulMod x y n = snd (BigInteger.DivRem(x * y, n))
    let rec loop a b c =
        if b = 0I then c else
            let (bd, br) = BigInteger.DivRem(b, 2I)
            loop (mulMod a a n) bd (if br = 0I then c else (mulMod c a n))
    loop a b 1I


let modulo n m =
    let mod' = n % m
    if sign mod' >= 0 then mod'
    else abs m + mod'

let rec gcd (x: bigint) (y: bigint) =
    if y = 0I then x
    else gcd y (x % y)

let random n = // Generate a random number n bytes long
    let mutable bytes : byte array = Array.zeroCreate n
    (new System.Random()).NextBytes(bytes)
    abs (new BigInteger (bytes))

let rec ext_gcd (x:bigint) (y:bigint) =
    if y = 0I then
        (1I,0I)
    else
        let q = x/y
        let r = x - y*q
        let (s,t) = ext_gcd y r
        (t, s-q*t)


let coprime n = // Find a coprime of n
    let mutable test = random KEYSIZE
    while ((gcd n test) <> 1I) do 
        test <- random KEYSIZE
    test
let rec prime k = // Find a (probable) prime
    let x = random KEYSIZE
    let y = coprime x
    if modexp y (x-1I) x = 1I then x
    else prime k

let modmultinv (e:bigint) (n:bigint) =
    let (x,_) = ext_gcd e n
    modulo x n

let keys = 
    let p = prime 2
    let mutable q = prime 2 
    while p = q do q <- prime 2
    let n = p*q
    let phi = (p-1I)*(q-1I)
    let e = 65537I
    let d = modmultinv e phi
    ((n,e), (n,d))

let encrypt c (n, e) =
    modexp c e n 
   
let decrypt c (n,d) = 
    modexp c d n

let (pubkey, privkey) = keys

let encryptMsg (s: string) key = 
    let x = [for c in s -> (int)c |> bigint]
    [for m in x -> (encrypt m key)]

let decryptMsg (s:bigint list) key = 
    let x = [for c in s -> (decrypt c key)]
    [for c in x -> (int)c |> char] |> List.fold(fun acc c -> acc + (string c)) ""

let keylen ((n: bigint), (exp:bigint)) = 
    Array.length(n.ToByteArray())*8 + Array.length(exp.ToByteArray())*8
