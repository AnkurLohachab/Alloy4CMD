module Transaction

open DLTTypes
open User
open Asset           // brings in AssetModel, TokenType, unitVal, etc.
open util/integer    // for Int, +, <

// ————————————————————————————————————————————————————
// 1. Domains & Types (requirement e.1)
// ————————————————————————————————————————————————————

/**
 * A transferable token on-chain, reusing the AssetModel signature.
 */
sig Token extends AssetModel {}

/**
 * Identifiers for smart contract state variables.
 */
sig StateVar {}

/**
 * Transaction kinds: transfer of tokens, deploy of contracts, or invoke of existing contracts.
 */
abstract sig Type {}
one sig Transfer, Deploy, Invoke extends Type {}

/**
 * Value kinds carried by transactions.
 * - Zero: represents a zero amount.
// - PosValue: strictly positive amounts.
 */
abstract sig Value {}
one sig Zero extends Value {}
sig PosValue extends Value {}


// ————————————————————————————————————————————————————
// 2. History Linking (requirement e.4)
// ————————————————————————————————————————————————————

/**
 * Cryptographic hash linking transactions in a history DAG.
 */
sig Hash {
  prev: set Hash   // predecessor hashes
}

/**
 * Ensures the hash-history graph is acyclic.
 */
fact AcyclicHistory {
  no h: Hash | h in h.^prev
}


// ————————————————————————————————————————————————————
// 3. Payload Definitions (requirements e.1 & e.3)
// ————————————————————————————————————————————————————

/**
 * Abstract payload for transactions.
 */
abstract sig Payload {}

/**
 * Payload for token transfers.
 */
sig TransferPayload extends Payload {
  sender, receiver: one DLTUser,  // participants
  token           : one Token,    // token being transferred
  atTime          : one Time,     // timestamp of transfer
  amount          : one Value     // must be non-zero for valid transfers
}

/**
 * Payload for contract operations (deploy or invoke).
 */
sig ContractPayload extends Payload {
  assigns: StateVar -> one Value  // mapping of state variables to new values
}

/**
 * Opaque metadata container attached to each transaction.
 */
sig Metadata {}


// ————————————————————————————————————————————————————
// 4. Transaction Structure & Facts (requirements e.2 & e.3)
// ————————————————————————————————————————————————————

/**
 * On-chain transaction record.
 */
sig Transaction {
  hash    : one Hash,       // unique identifier
  tt      : one Type,       // transaction type
  payload : one Payload,    // associated payload
  meta    : one Metadata    // auxiliary metadata
}

/**
 * e.2: Ensures each Transaction hash is unique.
 */
fact UniqueTransactionHashes {
  all t1, t2: Transaction |
    t1 != t2 implies t1.hash != t2.hash
}

/**
 * e.3: Payload must match the declared transaction type:
 * - Transfer transactions use TransferPayload.
// - Deploy/Invoke use ContractPayload.
 */
fact PayloadTypeConsistency {
  all t: Transaction |
    (t.tt = Transfer implies t.payload in TransferPayload) &&
    (t.tt != Transfer implies t.payload in ContractPayload)
}

/**
 * e.3: Transfers must carry a positive amount.
 */
fact PositiveAmounts {
  all tp: TransferPayload | tp.amount != Zero
}


/**
 * Instantiate a small model to validate all transaction constraints.
 */
run {} for
    5 Transaction,
    5 TransferPayload, 5 ContractPayload,
    5 Hash, 5 Metadata,
    5 DLTUser, 5 Time, 5 State, exactly 1 First,
    5 AssetModel, 5 Token, 5 StateVar,
    5 Value, exactly 1 Zero, 5 PosValue,

    // All DLTTypes signatures
    5 DLTTypes/User,
    5 DLTTypes/Service,
    5 DLTTypes/Asset,
    5 DLTTypes/DLTAccount,
    5 DLTTypes/DLTAddress,
    5 DLTTypes/PublicKey,
    5 DLTTypes/PrivateKey,
    5 DLTTypes/KeyPair,
    5 DLTTypes/AddrDerivation,
    5 DLTTypes/Time,

    // And the User module’s
    5 User/DLTUser,
    5 User/ExternalUser,
    5 User/State,
    exactly 1 User/First
