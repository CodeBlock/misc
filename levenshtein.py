def levenshtein(a, b):
	cost = 0

	if len(a) == 0:
		return len(b)

	if len(b) == 0:
		return len(a)

	if a[0] != b[0]:
		cost = 1

	return min([levenshtein(a[1::], b) + 1,
				levenshtein(a, b[1::]) + 1,
				levenshtein(a[1::], b[1::]) + cost])
