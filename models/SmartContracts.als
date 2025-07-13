module SmartContracts

open DLTTypes      // brings in DLTAccount, DLTAddress, Time, etc.
open User          // brings in DLTUser, ExternalUser, State, First
open util/boolean  // for Bool, True, False

// ————————————————————————————————————————————————————————
// 1. Core contract-level domains
// ————————————————————————————————————————————————————————

/**
 * On-chain smart contract bytecode representation.
 */
sig Bytecode {}

/**
 * Identifiers for individual storage slots in a contract.
 */
sig StorageVar {}

/**
 * Generic values stored or computed by contracts.
 */
sig Value {}

/**
 * External oracle data source, with a set of pending requests.
 */
sig OracleSource {
  requests: set OracleRequest  // outstanding oracle queries
}

/**
 * An oracle query request, yielding a response value.
 */
sig OracleRequest {
  response: one OracleValue    // the value provided by the oracle
}

/**
 * The possible values returned by an oracle.
 */
sig OracleValue {}

/**
 * Confidentiality view exposing a subset of a contract’s state
 * to a particular DLTUser.
 */
sig View {
  user : one DLTUser,                          // the viewer
  sc   : one SmartContract,                    // contract being viewed
  vals : StorageVar -> lone Value              // storage entries visible to user
}

/**
 * Cross-chain contract subtype, supporting oracle calls.
 */
sig CrossChain extends SmartContract {}

/**
 * Oracle function for cross-chain contracts:
 * returns the set of values from a given source’s responses.
 */
fun oracle[c: CrossChain, src: OracleSource]: set OracleValue {
  src.requests.response
}


// ————————————————————————————————————————————————————————
// 2. Smart-contract bundle
// ————————————————————————————————————————————————————————

/**
 * Core smart contract signature.
 * - code: its deployed bytecode.
// - state: mapping from storage variables to stored values.
// - proxy/impl: upgrade-pattern pointers.
// - selfDestructed: indicates if contract has been destroyed.
// - redeployedTo: points to successor after self-destruct.
// - usesOracle: which external sources it may query.
 */
sig SmartContract {
  code           : one Bytecode,
  state          : StorageVar -> lone Value,
  proxy          : lone SmartContract,
  impl           : lone SmartContract,
  selfDestructed : one Bool,
  redeployedTo   : lone SmartContract,
  usesOracle     : set OracleSource
}


// ————————————————————————————————————————————————————————
// 3. Proxy–implementation upgrade pattern
// ————————————————————————————————————————————————————————

/**
 * Prevents cycles in proxy chains.
 */
fact ProxyAcyclic {
  no c: SmartContract | c in c.proxy.^proxy
}

/**
 * Proxies must share state layout with their target.
 */
fact ProxyStateAlias {
  all c: SmartContract |
    some c.proxy implies c.state = c.proxy.state
}

/**
 * Implementations must share code with their proxy.
 */
fact ProxyCodeAlias {
  all c: SmartContract |
    some c.impl implies c.impl.code = c.code
}


// ————————————————————————————————————————————————————————
// 4. Self-destruct & redeploy semantics
// ————————————————————————————————————————————————————————

/**
 * Once self-destructed, contract state is cleared.
 */
fact DestructClearsState {
  all c: SmartContract | c.selfDestructed = True implies no c.state
}

/**
 * Redeployment only occurs after self-destruct.
 */
fact RedeployFollowsDestruct {
  all c: SmartContract | some c.redeployedTo implies c.selfDestructed = True
}

/**
 * Redeployed contracts start fresh (new code, no prior state).
 */
fact RedeployFreshFields {
  all c: SmartContract |
    some c.redeployedTo implies
      c.redeployedTo.code != c.code &&
      no c.redeployedTo.state
}


// ————————————————————————————————————————————————————————
// 5. Oracle-integration consistency
// ————————————————————————————————————————————————————————

/**
 * A contract may only use an oracle source if it has requests.
 */
fact OracleUsage {
  all c: SmartContract, os: OracleSource |
    os in c.usesOracle implies some os.requests
}

/**
 * Cross-chain contracts must integrate at least one oracle.
 */
fact CrossChainOracle {
  all c: CrossChain | some src: OracleSource | src in c.usesOracle
}


// ————————————————————————————————————————————————————————
// 6. Confidentiality-view consistency
// ————————————————————————————————————————————————————————

/**
 * Views can only expose storage entries that actually exist.
 */
fact ViewConsistency {
  all v: View |
    v.vals in v.sc.state
}



/**
 * Instantiate a small model to verify constraints.
 */
run {} for
  exactly 5 SmartContract, exactly 2 CrossChain,
  5 Bytecode, 5 StorageVar, 5 Value,
  3 OracleSource, 5 OracleRequest, 5 OracleValue,
  5 View,
  5 DLTTypes/User, 5 DLTTypes/Service, 5 DLTTypes/Asset,
  5 DLTTypes/DLTAccount, 5 DLTTypes/DLTAddress,
  5 DLTTypes/PublicKey, 5 DLTTypes/PrivateKey,
  5 DLTTypes/KeyPair, 5 DLTTypes/AddrDerivation,
  5 DLTTypes/Time,
  5 User/DLTUser, 5 User/ExternalUser,
  5 User/State, exactly 1 User/First
