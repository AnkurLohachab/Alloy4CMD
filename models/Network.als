module Network

open PeerNodes            // brings in PeerNode, FullNode, LightNode, BlockId, etc.
open Ledger               // brings in BlockRec, BlockMeta (and consolidated BlockId)
open util/integer         // for Int, +, ≥, sum

// ————————————————————————————————————————————————————————
// 1. Gossip events: peer‐to‐peer block dissemination
// ————————————————————————————————————————————————————————
/**
 * Represents a gossip message sent between nodes.
 * - sender, receiver: the participating PeerNodes.
// - blk: the block being gossiped.
// - sizeBytes: message size in bytes.
// - at: timestamp when the gossip occurs.
 */
sig Gossip {
  sender, receiver : one PeerNode,
  blk              : one BlockId,
  sizeBytes        : one Int,
  at               : one Int
}

// ————————————————————————————————————————————————————————
// 2. Knowledge: when a node learns about a block
// ————————————————————————————————————————————————————————
/**
 * Records the time at which a node first realizes a block exists.
 * - node: the PeerNode acquiring knowledge.
// - blk: the block in question.
// - realizedAt: timestamp of discovery.
 */
sig Knowledge {
  node       : one PeerNode,
  blk        : one BlockId,
  realizedAt : one Int
}

// ————————————————————————————————————————————————————————
// 3. Metrics: per‐node traffic accounting
// ————————————————————————————————————————————————————————
/**
 * Aggregated traffic metrics for a node.
 * - node: the PeerNode.
// - sentBytes: total bytes sent.
// - recvBytes: total bytes received.
 */
sig Metrics {
  node      : one PeerNode,
  sentBytes : one Int,
  recvBytes : one Int
}

// ————————————————————————————————————————————————————————
// 4. Topology constraints: valid peer communications
// ————————————————————————————————————————————————————————
/**
 * Ensures gossip only happens along established P2P links.
 */
fact PeerOnly {
  all g: Gossip | g.receiver in g.sender.peers
}

/**
 * Disallow self‐gossip.
 */
fact NoSelfGossip {
  no g: Gossip | g.sender = g.receiver
}

// ————————————————————————————————————————————————————————
// 5. Temporal constraints: logical time bounds
// ————————————————————————————————————————————————————————
/**
 * Timestamps must be non‐negative.
 */
fact NonNegativeTime {
  all g: Gossip    | g.at        >= Int[0]
  all k: Knowledge | k.realizedAt >= Int[0]
}

/**
 * Each (node, block) knowledge record is unique.
 */
fact UniqueKnowledgeTimestamp {
  all disj k1, k2: Knowledge |
    (k1.node = k2.node && k1.blk = k2.blk) implies k1 = k2
}

// ————————————————————————————————————————————————————————
// 6. Knowledge propagation: causality of gossip
// ————————————————————————————————————————————————————————
/**
 * A node can only gossip a block it already knows.
 */
fact GossipRequiresKnowledge {
  all g: Gossip |
    some k: Knowledge |
      k.node       = g.sender &&
      k.blk        = g.blk    &&
      k.realizedAt <= g.at
}

/**
 * Gossip creates knowledge at the receiver at the same time.
 */
fact GossipCreatesKnowledge {
  all g: Gossip |
    one k: Knowledge |
      k.node       = g.receiver &&
      k.blk        = g.blk      &&
      k.realizedAt = g.at
}

// ————————————————————————————————————————————————————————
// 7. Traffic metrics calculation
// ————————————————————————————————————————————————————————
/**
 * Computes sentBytes as the sum of sizes of all gossips sent by the node.
 */
fact ComputeSentBytes {
  all m: Metrics |
    m.sentBytes = sum[m.node.~sender.sizeBytes]
}

/**
 * Computes recvBytes as the sum of sizes of all gossips received by the node.
 */
fact ComputeRecvBytes {
  all m: Metrics |
    m.recvBytes = sum[m.node.~receiver.sizeBytes]
}

// ————————————————————————————————————————————————————————
// 8. check assertion: combined gossip‐knowledge consistency
// ————————————————————————————————————————————————————————
/**
 * Ensures every gossip event is both preceded by sender’s knowledge
 * and yields receiver’s knowledge at the same timestamp.
 */
assert NetworkWellFormed {
  all g: Gossip |
    // sender knew the block before or at gossip time
    some k1: Knowledge |
      k1.node       = g.sender &&
      k1.blk        = g.blk    &&
      k1.realizedAt <= g.at
    &&
    // receiver learns block exactly at gossip time
    some k2: Knowledge |
      k2.node       = g.receiver &&
      k2.blk        = g.blk    &&
      k2.realizedAt = g.at
}

/**
 * Bounded check of NetworkWellFormed in a small network.
 */
check NetworkWellFormed for
  3 Gossip,
  3 Knowledge,
  3 Metrics,
  3 PeerNode, 3 FullNode, 3 LightNode,
  4 Role, exactly 1 Validator, exactly 1 Miner, exactly 1 Archive, exactly 1 Observer,
  3 BlockMeta, 3 BlockId, 3 BlockRec,
  3 User, 3 Service, 3 Asset, 3 DLTAccount, 3 DLTAddress,
  3 PublicKey, 3 PrivateKey, 3 KeyPair, 3 AddrDerivation, 3 Time,
  3 State, 3 StateVar, 3 Value, 3 Hash, 3 Payload, 3 Metadata, 3 Transaction
