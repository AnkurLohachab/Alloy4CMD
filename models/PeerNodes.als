module PeerNodes

open util/integer // for Int, ≥, >

// ————————————————————————————————————————————————————————
// f.1: PeerNode partitions (Full vs. Light)
// ————————————————————————————————————————————————————————

/**
 * Unique identifiers for blockchain blocks.
 */
sig BlockId {}

/**
 * Roles that a peer node can hold in the network.
 * - Validator: participates in consensus validations.
// - Miner: creates new blocks.
// - Archive: stores full chain history.
// - Observer: lightweight monitoring node.
 */
abstract sig Role {}
one sig Validator, Miner, Archive, Observer extends Role {}

/**
 * Represents a node in the peer‐to‐peer network.
 * - roles: set of roles this node fulfills (requirement f.2).
 * - peers: its direct P2P connections (requirement f.3).
 * - sync:  the set of blocks it knows about (f.4–f.5).
 * - storageCap: its disk/storage capacity (added realism).
 * - bandwidthCap: its network bandwidth capacity (added realism).
 */
sig PeerNode {
  roles:        set Role,
  peers:        set PeerNode,
  sync:         set BlockId,
  storageCap:   one Int,
  bandwidthCap: one Int
}

/**
 * Two concrete partitions of PeerNode:
 * - FullNode: maintains full chain state.
// - LightNode: only partial sync.
 */
sig FullNode, LightNode extends PeerNode {}

/**
 * f.1: FullNode and LightNode together cover all PeerNode instances.
 */
fact Partition {
  FullNode + LightNode = PeerNode
}


// ————————————————————————————————————————————————————————
// f.2: Role‐assignment constraints
// ————————————————————————————————————————————————————————

/**
 * Every PeerNode must have at least one role.
 */
fact RolesNonEmpty {
  all n: PeerNode | some n.roles
}

/**
 * Archive nodes must be full nodes (must store entire chain history).
 */
fact ArchiveOnlyFull {
  all n: PeerNode | Archive in n.roles implies n in FullNode
}


// ————————————————————————————————————————————————————————
// f.3: P2P graph properties
// ————————————————————————————————————————————————————————

/**
 * No node is connected to itself.
 */
fact P2PIrreflexive {
  no n: PeerNode | n in n.peers
}

/**
 * Peer connections are bidirectional.
 */
fact P2PSymmetric {
  all n1, n2: PeerNode |
    n2 in n1.peers implies n1 in n2.peers
}


// ————————————————————————————————————————————————————————
// f.4–f.5: Synchronization constraints
// ————————————————————————————————————————————————————————

/**
 * Full nodes know every block in the network.
 */
fact FullSyncComplete {
  all n: FullNode | n.sync = BlockId
}

/**
 * Light nodes have only a strict subset of blocks.
 */
fact LightSyncPartial {
  all n: LightNode | n.sync != BlockId
}


/**
 * Capacities must be non-negative.
 */
fact NonNegativeCapacity {
  all n: PeerNode |
    n.storageCap >= 0 and n.bandwidthCap >= 0
}

/**
 * Full nodes are expected to have substantial storage.
 */
fact FullNodeHighStorage {
  all n: FullNode | n.storageCap > 1000
}


/**
 * Runs a small model to ensure the partitioning
 * and constraints can be satisfied.
 */
run {} for
    7 PeerNode,
    3 FullNode, 4 LightNode,
    10 BlockId,
    exactly 1 Validator, exactly 1 Miner, exactly 1 Archive, exactly 1 Observer,
    5 Int
