module Ledger

open DLTTypes        // brings in DLTAddress, DLTAccount, AddrDerivation, Time
open User            // brings in DLTUser, ExternalUser, State, First
open PeerNodes       // brings in PeerNode, FullNode, LightNode, BlockId
open Transaction     // brings in Transaction, Hash, Payload, Metadata, StateVar, Token
open util/integer    // for Int, +, >=

// —————————————————————————————————————————————
// 1. Block metadata
// —————————————————————————————————————————————

/**
 * Metadata attached to each block.
 * - timestamp: when the block was created.
 * - nonce: consensus-generated number.
 * - merkleRoot: authenticated-data-structure root (e.g., Merkle Patricia root).
 */
sig BlockMeta {
  timestamp : one Time,
  nonce     : one Int,
  merkleRoot: one DLTAddress
}


// —————————————————————————————————————————————
// 2. Block records (linear vs. DAG)
// —————————————————————————————————————————————

/**
 * A block record in the ledger.
 * - id: unique identifier for the block.
 * - data: the set of transactions included.
 * - prev: predecessor in a linear chain (at most one).
 * - parents: parent set in a DAG view (zero or more).
 * - meta: the block’s metadata.
 */
sig BlockRec {
  id      : one BlockId,
  data    : set Transaction,
  prev    : lone BlockRec,
  parents : set BlockRec,
  meta    : one BlockMeta
}

/**
 * The unique genesis block with no predecessors or parents.
 */
one sig Genesis extends BlockRec {}
fact GenesisBase {
  no Genesis.prev
  no Genesis.parents
}

/**
 * g.2: Each non-genesis block is either a linear successor
 *      (one prev, no parents) or a DAG node (some parents, no prev).
 */
fact ChainOrDAG {
  all b: BlockRec - Genesis |
    (one b.prev and no b.parents) or
    (some b.parents and no b.prev)
}

/**
 * g.3: No cycles in the linear chain.
 */
fact LinearAcyclic {
  no b: BlockRec | b in b.^prev
}

/**
 * g.4: No cycles in the DAG of parent links.
 */
fact DAGAcyclic {
  no b: BlockRec | b in b.^parents
}

/**
 * g.5: All block identifiers are distinct.
 */
fact UniqueBlockIds {
  all disj b1, b2: BlockRec | b1.id != b2.id
}

/**
 * g.6: A transaction cannot appear in more than one block.
 */
fact TxUniqueness {
  no t: Transaction |
    some disj b1, b2: BlockRec | t in b1.data and t in b2.data
}

/**
 * Ancestor function for the linear chain.
 */
fun ancestors[b: BlockRec]: set BlockRec { b.^prev }

/**
 * g.7: Append-only property on linear chain:
 *      all ancestor transactions are included in the block’s data.
 */
fact AppendOnlyLinear {
  all b: BlockRec |
    some b.prev implies ancestors[b].data in b.data
}

/**
 * g.8: Each block’s Merkle root must be defined.
 */
fact RootWellFormed {
  all b: BlockRec | some b.meta.merkleRoot
}


// —————————————————————————————————————————————
// 3. Heights (optional indexing)
// —————————————————————————————————————————————

/**
 * Height of a block in the linear chain: number of predecessors.
 */
fun height[b: BlockRec]: Int { #(b.^prev) }

/**
 * Heights increase by one along the linear chain.
 */
fact HeightMonotonic {
  all b: BlockRec | some b.prev implies height[b] = height[b.prev] + 1
}


// —————————————————————————————————————————————
// 4. Full- vs. Light-node views
// —————————————————————————————————————————————

/**
 * Full nodes see all blocks.
 */
fact FullNodeSeesAll {
  all n: FullNode | n.sync = BlockId
}

/**
 * Light nodes see only a strict subset of blocks.
 */
fact LightNodePartial {
  all n: LightNode | n.sync != BlockId
}


/**
 * Predicate to check a purely linear chain structure.
 */
pred linearChainOK {
  all b: BlockRec |
    (b = Genesis  => (no b.prev and no b.parents)) and
    (b != Genesis => (one b.prev and no b.parents))
}

/**
 * Check linearChainOK in a bounded scope.
 */
run linearChainOK for
    5 Int,
    5 BlockRec, 5 BlockMeta, 5 Transaction, 5 Time,
    5 DLTAddress, 5 DLTAccount, 5 AddrDerivation,
    5 BlockId,
    5 PeerNode, 3 FullNode, 4 LightNode,
    5 DLTUser, 5 ExternalUser, 5 State, exactly 1 First,
    5 Hash, 5 Payload, 5 Metadata, 5 StateVar, 5 Token,
    5 Service, 5 Asset,
    5 PublicKey, 5 PrivateKey, 5 KeyPair,
    5 Value, exactly 1 Zero, 5 PosValue

/**
 * Predicate to check a DAG-based ledger (every non-genesis block has parents).
 */
pred dagLedgerOK {
  all b: BlockRec - Genesis | some b.parents
}

/**
 * Check dagLedgerOK in a bounded scope.
 */
run dagLedgerOK for
    5 Int,
    5 BlockRec, 5 BlockMeta, 5 Transaction, 5 Time,
    5 DLTAddress, 5 DLTAccount, 5 AddrDerivation,
    5 BlockId,
    5 PeerNode, 3 FullNode, 4 LightNode,
    5 DLTUser, 5 ExternalUser, 5 State, exactly 1 First,
    5 Hash, 5 Payload, 5 Metadata, 5 StateVar, 5 Token,
    5 Service, 5 Asset,
    5 PublicKey, 5 PrivateKey, 5 KeyPair,
    5 Value, exactly 1 Zero, 5 PosValue
