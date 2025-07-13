module DLTSystem

open DLTTypes
open User
open Wallet
open Transaction
open Ledger
open PeerNodes
open Consensus
open SmartContracts
open Service
open Asset
open SoftwareClients
open Oracles
open Telemetry
open Crypto

// -----------------------------------------------------------------------------
// 1. No‐double‐spend (UTXO style)
//    Ensure that no two transfers in the same block spend the same token.
// -----------------------------------------------------------------------------

/**
 * Asserts that within any single block’s transaction set,
 * there are no two distinct TransferPayloads operating on the same token.
 */
assert NoDoubleSpend {
  no disj t1, t2: Transaction |
    // both transactions must be token transfers
    t1.payload in TransferPayload &&
    t2.payload in TransferPayload &&
    // they must reference the same token
    (t1.payload).token = (t2.payload).token &&
    // and both must appear together in some block
    some b: BlockRec | t1 in b.data && t2 in b.data
}


// -----------------------------------------------------------------------------
// 2. Consensus & ledger agree on chain‐head visibility
//    Every decision by a non‐faulty node occurs only after that node
//    has at least one block in its sync set.
// -----------------------------------------------------------------------------

/**
 * Asserts that for every Decision made by a non‐faulty node,
 * the node’s sync set already contains at least one block identifier.
 */
assert DecisionImpliesLedgerTip {
  all d: Decision |
    let n = d.decider |
      some b: BlockRec | b.id in n.sync
}


// -----------------------------------------------------------------------------
// 3. Membership enforcement (Corollary)
//    Only direct (on‐chain) users may invoke services.
// -----------------------------------------------------------------------------

/**
 * Asserts that any usage of a service by a user at time t
 * must be by a DLTUser in the initial state’s direct‐user set.
 */
assert OnlyDUInvokesService {
  all s: UsableService, u: DLTUser, t: Time |
    t in s.usedBy[u] implies u in First.DU
}


// -----------------------------------------------------------------------------
// 4. Checks
// -----------------------------------------------------------------------------

// Check no‐double‐spend in a small model with transfers and blocks
check NoDoubleSpend 

// Check consensus/ledger agreement
check DecisionImpliesLedgerTip

// Check that only direct users invoke services
check OnlyDUInvokesService 
