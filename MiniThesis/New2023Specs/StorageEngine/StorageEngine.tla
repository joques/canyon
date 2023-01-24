--------------------------- MODULE StorageEngine ---------------------------
EXTENDS TLC, Intergers, Sequences, Naturals

CONSTANTS
MaxKeys, Order
(* You might want to define MaxKeys to use it in variables
 or we can assume Maxkeys is a set of all real Numbers
MaxKeys is a set of all Real numbers
 
*)

ASSUME /\ MaxKeys \in NAt \ {0}


(*
These Variables are just Arrays for holding a set of different data types
*)

(*
VARIABLE object, controlState, subControlState, key, Ver, Edges, Path

TypeOK == /\ controlState \in {"Start", "middle", "done"}
          /\ subControlState \in {"Lf", "Pt", "Co"}
          /\ key  \in [Nodes -> Nodes]
          /\ Ver \in [Nodes -> Nat]
          
ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)
*)

VARIABLES values, versions, deleted, keys

TypeOK == /\ values \in [0..MaxKeys-1] 
          /\ versions \in [0..MaxKeys-1]
          /\ deleted \in [0..MaxKeys-1]
          /\ keys \in [0..MaxKeys-1]
          
-----------------------------------------------------------------------------    
\*root == INSTANCE BPlusTree With root <- root, Order <- Order , keys <- KeyType 
-----------------------------------------------------------------------------


TypeInvariant ==
/\ root \in BPlusTree
/\ keys[i] /= keys[j] for all i, j
/\ values[i] /= values[j] for all i, j
/\ keys[i] /= "deleted" for all i

Init ==
/\ root = emptyTree
/\ keys = [["deleted"] |-> (MaxKeys-1)]
/\ values = [["deleted"] |-> (MaxKeys-1)]
/\ versions = [0 |-> (MaxKeys-1)]
/\ deleted = [FALSE |-> (MaxKeys-1)]

Create(key, value) ==
/\ key /= "deleted"
/\ keys' = [keys EXCEPT ![i] = key]
/\ values' = [values EXCEPT ![i] = value]
/\ versions' = [versions EXCEPT ![i] = 1]
/\ deleted' = [deleted EXCEPT ![i] = FALSE]
/\ i' = (i + 1) \mod MaxKeys
/\ root' = Insert(root, key, i)
/\ Next = Create(key, value)

Read(key) ==
/\ key /= "deleted"
/\ EXISTS i \in 0..MaxKeys-1 : key = keys[i]
/\ value = values[i]
/\ version = versions[i]
/\ Next = Read(key)

Update(key, value, version) ==
/\ key /= "deleted"
/\ EXISTS i \in 0..MaxKeys-1 : key = keys[i]
/\ version < versions[i]
/\ deleted[i] = FALSE
/\ keys' = keys
/\ values' = [values EXCEPT ![i] = value]
/\ versions' = [versions EXCEPT ![i] = version + 1]
/\ deleted' = deleted
/\ root' = Update(root, key, i)
/\ Next = Update(key, value, version)

Delete(key, version) ==
/\ key /= "deleted"
/\ EXISTS i \in 0..MaxKeys-1 : key = keys[i]
/\ version < versions[i]
/\ deleted[i] = FALSE
/\ keys' = keys
/\ values' = values
/\ versions' = [versions EXCEPT ![i] = version + 1]
/\ deleted' = [deleted EXCEPT ![i] = TRUE]
/\ root' = root
/\ Next = Delete(key, version)

Spec ==
/\ Init
/\ [][Next]_<<keys, values, versions, deleted, root>>

=============================================================================
\* Modification History
\* Last modified Tue Jan 24 03:02:37 CAST 2023 by goodwill
\* Created Sat Jan 14 19:11:17 CAST 2023 by goodwill
