class Node:
	def __init__(self, val, weight, children=None):
		self.val = val
		self.weight = weight
		self.children = children
		
def huffmantree(string):
	occurences = {}
	for c in string:
		if not c in occurences.keys():
			occurences[c] = 1
		else:
			occurences[c] += 1

	nodes = []
	for val, occurence in occurences.items():
		nodes.append(Node(val, occurence))

	while len(nodes) >= 2:
		nodes.sort(key=lambda x: x.weight, reverse=True)
		children = [nodes.pop(), nodes.pop()]
		parent = Node(None, children[0].weight + children[1].weight, children=children)
		nodes.append(parent)

	return nodes[0] # Root node

def huffmanencode(string, tree=None):
	if tree:
		return (tree, [getsym(tree, c) for c in string])
	else:
		tree = huffmantree(string)
		return (tree, [getsym(tree, c) for c in string])

def huffmandecode(tree, string):
	#return [getval(tree, s) for s in syms]
	string = list(string)[::-1]
	vals = []
	sym = ""
	while(len(string) > 0):
		try:
			sym += string.pop()
			val = getval(tree, sym)
			vals.append(val)
			sym = ""
		except Exception:
			continue
	return vals


def getsym(root, val, sofar=""):
	if root.children:
		childresults = [getsym(root.children[0], val, "0" + sofar), getsym(root.children[1], val, "1" + sofar)]
		if childresults[0]:
			return childresults[0]
		else:
			return childresults[1]
	else:
		if root.val == val:
			return sofar[::-1]
		else:
			return None		

def getval(root, symbol):
	if root.children:
		if symbol[0] == '0':
			return getval(root.children[0], symbol[1:])
		else:
			return getval(root.children[1], symbol[1:])
	else:
		return root.val
