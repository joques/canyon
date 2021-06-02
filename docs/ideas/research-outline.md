Research Outline
================

short intro...

# Description

provide a short description of the research project

A storage engine is an internal software component that a data store uses to store, read, update and delete data in the underlying memory and storage system.

# Key Features

The following features will be part of system requirements:

* related to the storage system
	* distributed B+Trees and LSM for reading, writing and updating
	* persistent data
	* content-addressable data
	* data versioning (to stregthen collaboration)
	* maybe compression
	* will have to choose one or several data models (key-value, document, graph and wide-column)
* related to distributed systems
	* replication, concurrency and consensus
	* membership (with gossip style)


# Topics

short description of the topics involved in this research

data structures: LSM and B-Trees (including B+Trees)

a few DFS: Gluster FS, HDFS, BeeGFS, Lustre

write-ahead log and write-through cache

storage devices (raw devices) and how to write straight to devices

# Storage Engines

* Berkeley DB and Level DB
* RocksDB and LMDB
* Sophia, HaloDB, libmdbx, BoltDB, WiredTiger

* More on DS
Lazy B-Tree
Two-component LSM tree
Copy-on-write for immutability
LSM tree for immutability
BwTree
