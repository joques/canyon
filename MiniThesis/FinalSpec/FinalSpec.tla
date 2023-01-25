----------------------------- MODULE FinalSpec -----------------------------

CONSTANTS
MaxKeys, Order

VARIABLES
keys[0..MaxKeys-1], values[0..MaxKeys-1], versions[0..MaxKeys-1], deleted[0..MaxKeys-1]
root

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

Read(key) ==
/\ key /= "deleted"
/\ EXISTS i \in 0..MaxKeys-1 : key = keys[i]
/\ value = values[i]
/\ version = versions[i]

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



=============================================================================
\* Modification History
\* Last modified Tue Jan 24 18:49:09 CAST 2023 by goodwill
\* Created Tue Jan 24 18:45:59 CAST 2023 by goodwill
