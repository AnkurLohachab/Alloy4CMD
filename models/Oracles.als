module Oracles

open SmartContracts    // brings in OracleSource, OracleRequest, OracleValue, CrossChain, oracle/1
open SoftwareClients  // brings in Client
open util/integer     // for Int, ≥

// ————————————————————————————————————————————————————————
// 1. Attach client‐side metadata to each request
// ————————————————————————————————————————————————————————

/**
 * Metadata for an on‐chain oracle request, recording:
 * - req: the on‐chain OracleRequest
 * - issuer: which off‐chain Client issued it
 * - at: timestamp of issuance
 * - query: the query string payload
 */
sig ReqMeta {
  req    : one OracleRequest,
  issuer : one Client,
  at     : one Int,
  query  : one String
}

/**
 * Ensure a bijection between on‐chain requests and client metadata:
 * - every OracleRequest has exactly one ReqMeta
 * - every ReqMeta refers to exactly one OracleRequest
 */
fact ReqMetaBijection {
  all r: OracleRequest | one m: ReqMeta | m.req = r
  all m: ReqMeta       | one m.req
}


// ————————————————————————————————————————————————————————
// 2. Attach off‐chain metadata to each response
// ————————————————————————————————————————————————————————

/**
 * Metadata for an on‐chain oracle response, recording:
 * - val: the on‐chain OracleValue
 * - at: timestamp of arrival
 * - data: the returned data string
 */
sig ValMeta {
  val  : one OracleValue,
  at   : one Int,
  data : one String
}

/**
 * Ensure a bijection between on‐chain values and off‐chain metadata:
 * - every OracleValue has exactly one ValMeta
 * - every ValMeta refers to exactly one OracleValue
 */
fact ValMetaBijection {
  all v: OracleValue | one m: ValMeta | m.val = v
  all m: ValMeta     | one m.val
}


// ————————————————————————————————————————————————————————
// 3. Consistency between request and response
// ————————————————————————————————————————————————————————

/**
 * Link responses to their original requests:
 * the ValMeta.val must match the OracleRequest.response.
 */
fact ResponseMatchesRequest {
  all r: OracleRequest, mV: ValMeta |
    mV.val = r.response
}

/**
 * Enforce temporal ordering:
 * a response cannot arrive before its request was issued.
 */
fact ResponseAfterRequest {
  all mR: ReqMeta, mV: ValMeta |
    mV.val = mR.req.response implies mV.at >= mR.at
}


// ————————————————————————————————————————————————————————
// 4. Coherence assertion and check
// ————————————————————————————————————————————————————————

/**
 * Ensure every on‐chain request in each OracleSource
 * has corresponding client‐side metadata.
 */
assert OracleCoherent {
  all os: OracleSource |
    all r: os.requests |
      some m: ReqMeta | m.req = r
}

// Bounded check to validate the OracleCoherent assertion.
check OracleCoherent for
  10 Int,
  exactly 5 String,
  3 Bytecode, 3 StorageVar, 3 Value, 3 View,
  3 OracleSource, 3 OracleRequest, 3 OracleValue,
  3 ReqMeta, 3 ValMeta, 3 Client,
  3 SmartContract, 3 CrossChain,
  3 DLTAccount, 3 DLTAddress,
  3 PublicKey, 3 PrivateKey, 3 KeyPair,
  3 AddrDerivation, 3 Time,
  3 Service, 3 Asset,
  3 DLTUser, 3 ExternalUser,
  3 State, exactly 1 First,
  exactly 1 True, exactly 1 False,
  4 Vendor, exactly 1 Geth, exactly 1 Besu,
  exactly 1 Nethermind, exactly 1 Prysm,
  3 Version, 2 CRole,
  exactly 1 Execution, exactly 1 Consensus,
  3 WalletClient, 3 NodeClient,
  3 LightClient, 3 FullClient,
  3 DLTUserWallet, 3 WalletMeta,
  2 ConnType, exactly 1 Hot, exactly 1 Cold,
  2 CustodyType, exactly 1 Custodial, exactly 1 NonCustodial
