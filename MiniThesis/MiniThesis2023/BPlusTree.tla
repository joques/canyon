----------------------------- MODULE BPlusTree -----------------------------
EXTENDS Naturals

CONSTANT K

ASSUME K \in Nat \ {0}

(* -- VARIABLE DECLARATION -- *)
VARIABLE root

(* -- B+TREE NODE STRUCTURE -- *)
bpt_node(keys, children) == [ keys |-> keys, children |-> children ]
             \* The keys and children arrays of a B+tree node

(* -- INITIALIZATION -- *)
Init == root = [ keys |-> <<>>, children |-> <<>> ]

(* -- INSERTION -- *)
AddToEmptyRoot(new_key) ==
    root := [ keys |-> <<new_key>>, children |-> <<>> ]
    
AddToNonEmptyRoot(new_key) ==
    LET node == root
    IN
        IF Len(node.children) = 0 THEN 
            (* the node is a leaf *)
            IF Len(node.keys) = 2*K-1 THEN
                (* the node is full *)
                root := [ keys |-> <<new_key>>, children |-> <<node>> ]
            ELSE
                (* add the key to the leaf node *)
                root.keys := root.keys \o <<new_key>>
            
        ELSE 
            (* the node is not a leaf *)
            LET i == CHOOSE i \in 1..Len(node.keys) :
                new_key <= node.keys[i]
            IN
                AddToNonEmptyRootChild(node.children[i], new_key, node.children[i+1])
       
        
AddToNonEmptyRootChild(left, new_key, right) ==
    IF Len(left.children) = 0 THEN
        (* the left node is a leaf *)
        IF Len(left.keys) < 2*K-1 THEN
            (* add the key to the left node *)
            left.keys := left.keys \o <<new_key>>
        ELSE
            (* split the left node *)
            LET AddToNonEmptyRootChild(new_left, new_right, key) == SplitNode(left, new_key, right)
            IN
                AddToNonEmptyRoot(key) /\ 
                root.children [i |-> IF i = Len(root.children) + 1 THEN new_right ELSE root.children[i]]
        ENDIF
    ELSE 
        (* the left node is not a leaf *)
        LET i == CHOOSE i \in 1..Len(left.keys) :
            new_key <= left.keys[i]
        IN
            AddToNonEmptyRootChild(left.children[i], new_key, left.children[i+1])
    ENDIF

SplitNode(node, new_key, right) ==
    LET split_point == 2*K
        split_key == node.keys[K]
        right_node == [ keys |-> node.keys[split_point+1..],
                        children |-> node.children[split_point+1..] ]
        left_node == [ keys |-> node.keys[1..split_point-1],
                       children |-> node.children[1..split_point] ]
    IN
        IF new_key <= split_key THEN
            (* add the new key to the left node *)
            (left_node, right_node, split_key)
        ELSE
            (* add the new key to the right node *)
            (left_node, right_node, new_key)
        ENDIF

(* -- DELETION -- *)
\* We will not delete anything here. 
\* Soft delete will be in the CRUD of the Storage engine. 


Spec == Init /\ Next[]_Vars




\*B+ tree needs to be inspiration for the CRUD operations and should be generic. and we use the B+ Tree to validate our code. 

\* Have the B+ Tree as per data structure
\* then have the steps in algorithm form for your CRUD and check with the B+ tree Generic. 

\*code with the Anotations. no prity print needed 
\*the repository should have the simplest format of the raw informations. 

\*source code of the spec. 

\*Green book text book by Algorithms and Data Structure for any course. 

=============================================================================
\* Modification History
\* Last modified Tue Aug 01 00:54:48 AZT 2023 by lubin
\* Last modified Tue Aug 01 00:48:10 AZT 2023 by Goodwill Khoa
\* Created Mon Jul 30 21:56:09 AZT 2023 by Goodwill Khoa
