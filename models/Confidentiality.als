module Confidentiality

open SmartContracts       // brings in SmartContract, StorageVar, Value, Bytecode, Oracle*, View, CrossChain
open User                 // brings in DLTUser, ExternalUser, State, First
open DLTTypes             // brings in DLTAddress, DLTAccount, PublicKey, PrivateKey, KeyPair, AddrDerivation, Time, Asset, Service
open util/integer         // for Int, #

// -----------------------------------------------------------------------------
// 1. View projection
// -----------------------------------------------------------------------------

/**
 * A confidentiality view exposing only a projection of
 * a contract’s full on‐chain storage to a particular user.
 */
sig ConfView {
  user : one DLTUser,               // the viewer
  sc   : one SmartContract,         // contract being viewed
  proj : StorageVar -> lone Value   // var→value pairs the user is allowed to see
}

/**
 * Fact: enforce that every projected (var→value) pair
 * actually appears in the smart contract’s on‐chain state.
 */
fact ProjectionSubsetFact {
  all v: ConfView |
    v.proj in v.sc.state
}

/**
 * Assertion: redundant check that ProjectionSubsetFact holds.
 */
assert ProjectionSubset {
  all v: ConfView |
    v.proj in v.sc.state
}
check ProjectionSubset


// -----------------------------------------------------------------------------
// 2. Pseudonym mapping
// -----------------------------------------------------------------------------

/**
 * Global network mapping each user to the set of
 * on‐chain addresses (pseudonyms) they control.
 */
one sig Network {
  addrOf: DLTUser -> set DLTAddress
}

/**
 * Inverse lookup: given an address, return all users
 * that map to it in the Network.addrOf relation.
 */
fun owners[a: DLTAddress]: set DLTUser {
  { u: DLTUser | u->a in Network.addrOf }
}


// -----------------------------------------------------------------------------
// 3. Privacy properties
// -----------------------------------------------------------------------------

// 3.1 Initial anonymity

/**
 * Base‐case anonymity: initially every address
 * could belong to any user.
 */
fun anon0[a: DLTAddress]: set DLTUser { DLTUser }

/**
 * Predicate: initial anonymity holds if anon0[a] = all users.
 */
pred InitialAnonymity {
  all a: DLTAddress |
    anon0[a] = DLTUser
}


// 3.2 k‐Anonymity

/**
 * A cluster of addresses that should provide collective anonymity.
 */
sig Cluster {
  members: set DLTAddress
}

/**
 * Anonymity set of a cluster: any user who controls
 * at least one address in that cluster.
 */
fun anonC[C: Cluster]: set DLTUser {
  { u: DLTUser | some a: C.members | u in owners[a] }
}

/**
 * Fact: enforce that each cluster’s anonymity set
 * is at least as large as the cluster (k‐anonymity).
 */
fact KAnonymityFact {
  all C: Cluster |
    #anonC[C] >= #C.members
}

/**
 * Assertion: redundant check for KAnonymityFact.
 */
assert KAnonymity {
  all C: Cluster |
    #anonC[C] >= #C.members
}
check KAnonymity


// 3.3 Unlinkability

/**
 * Predicate: full unlinkability holds if every cluster’s
 * anonymity set includes _all_ users.
 */
pred Unlinkability {
  all C: Cluster |
    anonC[C] = DLTUser
}


// 3.4 Pseudonymity chain

/**
 * Predicates for the standard pseudonymity chain:
 *   • NoBind        = no address bindings leak
 *   • Pseudonymity  = each address maps to exactly one user
 */
pred NoBind {
  no Network.addrOf
}

pred Pseudonymity {
  all u1, u2: DLTUser, a: DLTAddress |
    (u1->a in Network.addrOf and u2->a in Network.addrOf)
      implies u1 = u2
}

/**
 * Fact: enforce the entire privacy chain:
 *   NoBind ⇒ Pseudonymity ⇒ Unlinkability ⇒ InitialAnonymity
 */
fact PrivacyChainFact {
  (NoBind implies Pseudonymity)
    and (Pseudonymity implies Unlinkability)
    and (Unlinkability implies InitialAnonymity)
}

/**
 * Assertion: redundant check for the pseudonymity chain.
 */
assert PseudoAnonymityChain {
  (NoBind implies Pseudonymity)
    and (Pseudonymity implies Unlinkability)
    and (Unlinkability implies InitialAnonymity)
}
check PseudoAnonymityChain


// -----------------------------------------------------------------------------
// 4. run
// -----------------------------------------------------------------------------

run {} for
  5 ConfView,
  1 Network,
  5 SmartContract,
  5 StorageVar,
  5 Value,
  3 DLTAddress,
  3 DLTUser,
  3 Cluster,
  3 Bytecode,
  3 OracleSource,
  3 OracleRequest,
  3 OracleValue,
  3 View,
  3 Service,
  3 Asset,
  3 DLTAccount,
  3 PublicKey,
  3 PrivateKey,
  3 KeyPair,
  3 AddrDerivation,
  3 Time, 5 User, 5 State
