---
---
# Modeling DNS with Alloy

Alloy is a great tool to use for modeling an unfamiliar domain.
I've never quite had a grasp on how the DNS system works, and so it makes a great example of how to model a system for learning.

* [RFC1034]

[RFC1034]: https://datatracker.ietf.org/doc/html/rfc1034

## Domain name space

The domain name space is a tree, where each node corresponds to a domain name. Here's an example from [RFC1034]:

```
                                   |
                                   |
             +---------------------+------------------+
             |                     |                  |
            MIL                   EDU                ARPA
             |                     |                  |
             |                     |                  |
       +-----+-----+               |     +------+-----+-----+
       |     |     |               |     |      |           |
      BRL  NOSC  DARPA             |  IN-ADDR  SRI-NIC     ACC
                                   |
       +--------+------------------+---------------+--------+
       |        |                  |               |        |
      UCI      MIT                 |              UDEL     YALE
                |                 ISI
                |                  |
            +---+---+              |
            |       |              |
           LCS  ACHILLES  +--+-----+-----+--------+
            |             |  |     |     |        |
            XX            A  C   VAXA  VENERA Mockapetris

```

Here's an alloy model.


```alloy
sig DomainName {}

sig Node {
	domainName: disj DomainName,
	children: set Node
}
```

Let's make sure the nodes form a tree:

```alloy
fact "nodes from a tree" {

	// no cycles
	no iden & ^children

	// fully connected
	// there's node from which every node is reachable (the root)
	some root : Node | Node in root.*children
}
```
## Records

DNS is a system that lets you look up records by domain name.


```alloy
abstract sig Record {
	name: DomainName
}
```

There are a ton of different DNS record types, let's just model some common ones:

```alloy
sig A extends Record {
	value: set IPv4Address
}

sig IPv4Address {}

sig AAAA extends Record {
	value: set IPv6Address
}

sig IPv6Address {}

sig CNAME extends Record {
	value: DomainName
}

pred noRecordsHaveSameName[r: set Record] {
	all disj r1, r2: Record | no r1.name & r2.name
}

fact {
	noRecordsHaveSameName[A]
	noRecordsHaveSameName[AAAA]
	noRecordsHaveSameName[CNAME]
}
```

## Zones

From [RFC1034]:

> every zone has at least one node, and hence domain name, for which it is authoritative, and all of the nodes in a particular zone are connected.

```alloy
sig Zone {
	nodes: disj set Node,
	records: disj set Record
} {
	// at least one node
	some nodes

	// all of the nodes in a zone are connected
	all disj n1, n2 : nodes | (n1->n2 in ^children) or (n2->n1 in ^children)

	// all records are in a zone
	// All records are associated withe one of the owned nodes
	all r: records | r.name in nodes.domainName
}

fact "Every record is associated with exactly one zone" {
	all r: Record | one records.r
}

run { some Zone }
```

Apex of a zone:

```alloy
fun root[nodes: set Node] : Node {
	let r = children & (nodes -> nodes) |  {n : nodes | no (n & n.^r)}
}


fun apex[z: Zone] : Node {
	root[z.nodes]
}
```
