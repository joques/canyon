----------------------------- MODULE BPlusTree -----------------------------
EXTENDS Naturals



CONSTANTS
Order, KeyType ,Node, LeafNode, IndexNode

VARIABLES
root

NodeType(node) == node \in LeafNode \union IndexNode

LeafNode(node) == node \in LeafNode
IndexNode(node) == node \in IndexNode

EmptyLeafNode(node) ==
/\ LeafNode(node)
/\ node.keys = []
/\ node.values = []
/\ node.next = null

NonEmptyLeafNode(node) ==
/\ LeafNode(node)
/\ node.keys # []
/\ node.values # []
/\ node.next # null

EmptyIndexNode(node) ==
/\ IndexNode(node)
/\ node.keys = []
/\ node.children = []

NonEmptyIndexNode(node) ==
/\ IndexNode(node)
/\ node.keys # []
/\ node.children # []

NodeInvariant(node) ==
/\ LeafNode(node) =>
(node.keys.cardinality = node.values.cardinality)
/\ IndexNode(node) =>
(node.keys.cardinality + 1 = node.children.cardinality)

TreeInvariant ==
/\ (root = null) =>
(TypeInvariant /\ NodeType(root))
/\ (root # null) =>
(TypeInvariant /\ NodeInvariant(root) /
(\A child \in SUBSET root.children : TreeInvariant))

Init ==
/\ root = null

Insert(node, key, value) ==
/\ LeafNode(node)
/\ key \in KeyType
/\ value \in ObjectPath
/\ node' = Append(node, key, value)
/\ (node'.keys.cardinality > Order) =>
(node' = Split(node'))
/\ root' = (node = root) => node'

Search(node, key) ==
/\ LeafNode(node)
/\ key \in KeyType
/\ value = node.values[node.keys.IndexOf(key)]


SplitLeafNode(node, key, value) ==
/\ node.keys' = [node.keys EXCEPT ![i] = key]
/\ node.values' = [node.values EXCEPT ![i] = value]
/\ newNode.keys = [node.keys[Order-1]]
/\ newNode.values = [node.values[Order-1]]
/\ newNode.next = node.next
/\ node.keys = node.keys[0..Order-2]
/\ node.values = node.values[0..Order-2]
/\ node.next = newNode
/\ newParent.keys = [node.keys[Order-2]]
/\ newParent.children = [node, newNode]
/\ newParent


Append(node, key, value) ==
/\ LeafNode(node)
/\ key \in KeyType
/\ value \in ObjectPath
/\ i = node.keys.IndexOf(key)
/\ (i > 0) =>
(node.keys' = [node.keys[1..i-1], key, node.keys[i+1..-1]])
/\ (i = 0) =>
(node.keys' = [key, node.keys])
/\ (i = -1) =>
(node.keys' = node.keys)
/\ i = node.values.IndexOf(value

=============================================================================
\* Modification History
\* Last modified Tue Jan 24 03:19:13 CAST 2023 by goodwill
\* Created Sat Jan 14 19:13:52 CAST 2023 by goodwill
