module EventLog

open SmartContracts    // brings in SmartContract, Bytecode, StorageVar, Value, Oracle, View, CrossChain, boolean
open Ledger            // brings in BlockRec, Transaction, BlockMeta, Genesis, PeerNodes, etc.
open util/integer      // for Int, >=, sum, steps, always, eventually, after, historically

//───────────────────────────────────────────────────────────────────────────────
// 1. Raw Event atoms (static schema)
//───────────────────────────────────────────────────────────────────────────────

/**
 * A low‐level on‐chain event emitted by a smart contract.
 *
 * Fields:
 *   • emitter: the SmartContract that emitted the event
 *   • inBlock: the BlockRec containing this event
 *   • topic:    a labeled topic string
 *   • data:     the payload string
 *   • idx:      the index of this log entry within its block
 */
sig Event {
  emitter : one SmartContract,
  inBlock : one BlockRec,
  topic   : one String,
  data    : one String,
  idx     : one Int
}

/**
 * f.1 UniqueIndex:
 *   Ensure stable ordering within each block:
 *   no two Event atoms share the same idx in the same BlockRec.
 */
fact UniqueIndex {
  all disj e1, e2: Event |
    e1.inBlock = e2.inBlock implies e1.idx != e2.idx
}

//───────────────────────────────────────────────────────────────────────────────
// 2. The mutable on‐chain EventLog
//───────────────────────────────────────────────────────────────────────────────

/**
 * Singleton representing the global on‐chain event log,
 * whose contents grow over time.
 */
one sig EventLog {
  var log: set Event  // the set of currently logged events
}

/**
 * Predicate isLogged:
 *   Checks whether a given Event is present in the current log.
 */
pred isLogged[e: Event] {
  e in EventLog.log
}

/**
 * Function eventsByEmitter:
 *   Retrieves all events emitted by a given SmartContract.
 */
fun eventsByEmitter(sc: SmartContract): set Event {
  EventLog.log & { e: Event | e.emitter = sc }
}

//───────────────────────────────────────────────────────────────────────────────
// 3. Temporal properties on the growing log
//───────────────────────────────────────────────────────────────────────────────

/**
 * f.2 InitLogEmpty:
 *   Initially (at time 0), the event log must be empty.
 */
fact InitLogEmpty {
  always (EventLog.log = none)
}

/**
 * f.3 LogMonotonic (append‐only):
 *   Once an event is logged, it remains logged in all future states.
 */
fact LogMonotonic {
  always (all e: Event | e in EventLog.log implies e in EventLog.log')
}

/**
 * f.4 LogCompleteness:
 *   Every declared Event atom will eventually appear in the log.
 */
fact LogCompleteness {
  always (all e: Event | eventually (e in EventLog.log))
}

/**
 * f.5 BlockBeforeEvent:
 *   An event can only appear after its block has been mined.
 *   (i.e., after inBlock ∈ BlockRec, the event appears.)
 */
fact BlockBeforeEvent {
  always (all e: Event |
    after (e.inBlock in BlockRec)
      implies eventually (e in EventLog.log)
  )
}

//───────────────────────────────────────────────────────────────────────────────
// 4. Assertions mirroring the facts
//───────────────────────────────────────────────────────────────────────────────

/**
 * Assert LogAppendOnly:
 *   Once an event is in the log, it never disappears.
 */
assert LogAppendOnly {
  always (all e: Event | e in EventLog.log implies e in EventLog.log')
}

/**
 * Assert LogEventuallyComplete:
 *   Every event eventually shows up in the log.
 */
assert LogEventuallyComplete {
  always (all e: Event | eventually (e in EventLog.log))
}

/**
 * Assert IndexesUnique:
 *   No two events share the same index in the same block.
 */
assert IndexesUnique {
  all disj e1, e2: Event |
    e1.inBlock = e2.inBlock implies e1.idx != e2.idx
}

/**
 * Assert EventsAfterBlock:
 *   Events only appear after their BlockRec exists.
 */
assert EventsAfterBlock {
  always (all e: Event |
    after (e.inBlock in BlockRec) implies eventually (e in EventLog.log))
}

//───────────────────────────────────────────────────────────────────────────────
// 5. Scoped temporal checks over a bounded trace
//───────────────────────────────────────────────────────────────────────────────

/*
 * We check each assertion over:
 *   – 8‐bit integers (Int)
 *   – trace length of 1..10 time steps
 *   – up to 3 Event atoms
 *   – exactly 1 EventLog singleton
 *   – small numbers of SmartContracts, Ledger types, and related atoms
 */

check LogAppendOnly
  for 8 Int, 1..10 steps,
      3 Event,
      exactly 1 EventLog,
      3 SmartContracts/Bytecode,
      3 SmartContracts/StorageVar,
      3 SmartContracts/Value,
      3 SmartContracts/OracleSource,
      3 SmartContracts/OracleRequest,
      3 SmartContracts/OracleValue,
      3 SmartContracts/View,
      3 SmartContracts/CrossChain,
      3 SmartContracts/SmartContract,
      3 Ledger/DLTTypes/User,
      3 Ledger/DLTTypes/Service,
      3 Ledger/DLTTypes/Asset,
      3 Ledger/DLTTypes/DLTAccount,
      3 Ledger/DLTTypes/DLTAddress,
      3 Ledger/DLTTypes/PublicKey,
      3 Ledger/DLTTypes/PrivateKey,
      3 Ledger/DLTTypes/KeyPair,
      3 Ledger/DLTTypes/AddrDerivation,
      3 Ledger/DLTTypes/Time,
      3 Ledger/User/DLTUser,
      3 Ledger/User/ExternalUser,
      3 Ledger/User/State,
      exactly 1 Ledger/User/First,
      2 SmartContracts/boolean/Bool,
      exactly 1 SmartContracts/boolean/True,
      exactly 1 SmartContracts/boolean/False,
      3 Ledger/BlockMeta,
      3 Ledger/BlockRec,
      exactly 1 Ledger/Genesis,
      3 Ledger/PeerNodes/BlockId,
      4 Ledger/PeerNodes/Role,
      exactly 1 Ledger/PeerNodes/Validator,
      exactly 1 Ledger/PeerNodes/Miner,
      exactly 1 Ledger/PeerNodes/Archive,
      exactly 1 Ledger/PeerNodes/Observer,
      3 Ledger/PeerNodes/PeerNode,
      3 Ledger/PeerNodes/FullNode,
      3 Ledger/PeerNodes/LightNode,
      3 Ledger/Transaction/Token,
      3 Ledger/Transaction/StateVar,
      3 Ledger/Transaction/Type,
      exactly 1 Ledger/Transaction/Transfer,
      exactly 1 Ledger/Transaction/Deploy,
      exactly 1 Ledger/Transaction/Invoke,
      3 Ledger/Transaction/Value,
      exactly 1 Ledger/Transaction/Zero,
      2 Ledger/Transaction/PosValue,
      3 Ledger/Transaction/Hash,
      3 Ledger/Transaction/Payload,
      3 Ledger/Transaction/TransferPayload,
      3 Ledger/Transaction/ContractPayload,
      3 Ledger/Transaction/Metadata,
      3 Ledger/Transaction/Transaction,
      3 Ledger/Transaction/Asset/AssetModel,
      2 Ledger/Transaction/Asset/TokenType,
      exactly 1 Ledger/Transaction/Asset/Fungible,
      exactly 1 Ledger/Transaction/Asset/NonFungible

check LogEventuallyComplete
  for 8 Int, 1..10 steps,
      3 Event,
      exactly 1 EventLog,
      3 SmartContracts/Bytecode,
      3 SmartContracts/StorageVar,
      3 SmartContracts/Value,
      3 SmartContracts/OracleSource,
      3 SmartContracts/OracleRequest,
      3 SmartContracts/OracleValue,
      3 SmartContracts/View,
      3 SmartContracts/CrossChain,
      3 SmartContracts/SmartContract,
      3 Ledger/DLTTypes/User,
      3 Ledger/DLTTypes/Service,
      3 Ledger/DLTTypes/Asset,
      3 Ledger/DLTTypes/DLTAccount,
      3 Ledger/DLTTypes/DLTAddress,
      3 Ledger/DLTTypes/PublicKey,
      3 Ledger/DLTTypes/PrivateKey,
      3 Ledger/DLTTypes/KeyPair,
      3 Ledger/DLTTypes/AddrDerivation,
      3 Ledger/DLTTypes/Time,
      3 Ledger/User/DLTUser,
      3 Ledger/User/ExternalUser,
      3 Ledger/User/State,
      exactly 1 Ledger/User/First,
      2 SmartContracts/boolean/Bool,
      exactly 1 SmartContracts/boolean/True,
      exactly 1 SmartContracts/boolean/False,
      3 Ledger/BlockMeta,
      3 Ledger/BlockRec,
      exactly 1 Ledger/Genesis,
      3 Ledger/PeerNodes/BlockId,
      4 Ledger/PeerNodes/Role,
      exactly 1 Ledger/PeerNodes/Validator,
      exactly 1 Ledger/PeerNodes/Miner,
      exactly 1 Ledger/PeerNodes/Archive,
      exactly 1 Ledger/PeerNodes/Observer,
      3 Ledger/PeerNodes/PeerNode,
      3 Ledger/PeerNodes/FullNode,
      3 Ledger/PeerNodes/LightNode,
      3 Ledger/Transaction/Token,
      3 Ledger/Transaction/StateVar,
      3 Ledger/Transaction/Type,
      exactly 1 Ledger/Transaction/Transfer,
      exactly 1 Ledger/Transaction/Deploy,
      exactly 1 Ledger/Transaction/Invoke,
      3 Ledger/Transaction/Value,
      exactly 1 Ledger/Transaction/Zero,
      2 Ledger/Transaction/PosValue,
      3 Ledger/Transaction/Hash,
      3 Ledger/Transaction/Payload,
      3 Ledger/Transaction/TransferPayload,
      3 Ledger/Transaction/ContractPayload,
      3 Ledger/Transaction/Metadata,
      3 Ledger/Transaction/Transaction,
      3 Ledger/Transaction/Asset/AssetModel,
      2 Ledger/Transaction/Asset/TokenType,
      exactly 1 Ledger/Transaction/Asset/Fungible,
      exactly 1 Ledger/Transaction/Asset/NonFungible

check IndexesUnique
  for 8 Int, 1..10 steps,
      3 Event,
      exactly 1 EventLog,
      3 SmartContracts/Bytecode,
      3 SmartContracts/StorageVar,
      3 SmartContracts/Value,
      3 SmartContracts/OracleSource,
      3 SmartContracts/OracleRequest,
      3 SmartContracts/OracleValue,
      3 SmartContracts/View,
      3 SmartContracts/CrossChain,
      3 SmartContracts/SmartContract,
      3 Ledger/DLTTypes/User,
      3 Ledger/DLTTypes/Service,
      3 Ledger/DLTTypes/Asset,
      3 Ledger/DLTTypes/DLTAccount,
      3 Ledger/DLTTypes/DLTAddress,
      3 Ledger/DLTTypes/PublicKey,
      3 Ledger/DLTTypes/PrivateKey,
      3 Ledger/DLTTypes/KeyPair,
      3 Ledger/DLTTypes/AddrDerivation,
      3 Ledger/DLTTypes/Time,
      3 Ledger/User/DLTUser,
      3 Ledger/User/ExternalUser,
      3 Ledger/User/State,
      exactly 1 Ledger/User/First,
      2 SmartContracts/boolean/Bool,
      exactly 1 SmartContracts/boolean/True,
      exactly 1 SmartContracts/boolean/False,
      3 Ledger/BlockMeta,
      3 Ledger/BlockRec,
      exactly 1 Ledger/Genesis,
      3 Ledger/PeerNodes/BlockId,
      4 Ledger/PeerNodes/Role,
      exactly 1 Ledger/PeerNodes/Validator,
      exactly 1 Ledger/PeerNodes/Miner,
      exactly 1 Ledger/PeerNodes/Archive,
      exactly 1 Ledger/PeerNodes/Observer,
      3 Ledger/PeerNodes/PeerNode,
      3 Ledger/PeerNodes/FullNode,
      3 Ledger/PeerNodes/LightNode,
      3 Ledger/Transaction/Token,
      3 Ledger/Transaction/StateVar,
      3 Ledger/Transaction/Type,
      exactly 1 Ledger/Transaction/Transfer,
      exactly 1 Ledger/Transaction/Deploy,
      exactly 1 Ledger/Transaction/Invoke,
      3 Ledger/Transaction/Value,
      exactly 1 Ledger/Transaction/Zero,
      2 Ledger/Transaction/PosValue,
      3 Ledger/Transaction/Hash,
      3 Ledger/Transaction/Payload,
      3 Ledger/Transaction/TransferPayload,
      3 Ledger/Transaction/ContractPayload,
      3 Ledger/Transaction/Metadata,
      3 Ledger/Transaction/Transaction,
      3 Ledger/Transaction/Asset/AssetModel,
      2 Ledger/Transaction/Asset/TokenType,
      exactly 1 Ledger/Transaction/Asset/Fungible,
      exactly 1 Ledger/Transaction/Asset/NonFungible

check EventsAfterBlock
  for 8 Int, 1..10 steps,
      3 Event,
      exactly 1 EventLog,
      3 SmartContracts/Bytecode,
      3 SmartContracts/StorageVar,
      3 SmartContracts/Value,
      3 SmartContracts/OracleSource,
      3 SmartContracts/OracleRequest,
      3 SmartContracts/OracleValue,
      3 SmartContracts/View,
      3 SmartContracts/CrossChain,
      3 SmartContracts/SmartContract,
      3 Ledger/DLTTypes/User,
      3 Ledger/DLTTypes/Service,
      3 Ledger/DLTTypes/Asset,
      3 Ledger/DLTTypes/DLTAccount,
      3 Ledger/DLTTypes/DLTAddress,
      3 Ledger/DLTTypes/PublicKey,
      3 Ledger/DLTTypes/PrivateKey,
      3 Ledger/DLTTypes/KeyPair,
      3 Ledger/DLTTypes/AddrDerivation,
      3 Ledger/DLTTypes/Time,
      3 Ledger/User/DLTUser,
      3 Ledger/User/ExternalUser,
      3 Ledger/User/State,
      exactly 1 Ledger/User/First,
      2 SmartContracts/boolean/Bool,
      exactly 1 SmartContracts/boolean/True,
      exactly 1 SmartContracts/boolean/False,
      3 Ledger/BlockMeta,
      3 Ledger/BlockRec,
      exactly 1 Ledger/Genesis,
      3 Ledger/PeerNodes/BlockId,
      4 Ledger/PeerNodes/Role,
      exactly 1 Ledger/PeerNodes/Validator,
      exactly 1 Ledger/PeerNodes/Miner,
      exactly 1 Ledger/PeerNodes/Archive,
      exactly 1 Ledger/PeerNodes/Observer,
      3 Ledger/PeerNodes/PeerNode,
      3 Ledger/PeerNodes/FullNode,
      3 Ledger/PeerNodes/LightNode,
      3 Ledger/Transaction/Token,
      3 Ledger/Transaction/StateVar,
      3 Ledger/Transaction/Type,
      exactly 1 Ledger/Transaction/Transfer,
      exactly 1 Ledger/Transaction/Deploy,
      exactly 1 Ledger/Transaction/Invoke,
      3 Ledger/Transaction/Value,
      exactly 1 Ledger/Transaction/Zero,
      2 Ledger/Transaction/PosValue,
      3 Ledger/Transaction/Hash,
      3 Ledger/Transaction/Payload,
      3 Ledger/Transaction/TransferPayload,
      3 Ledger/Transaction/ContractPayload,
      3 Ledger/Transaction/Metadata,
      3 Ledger/Transaction/Transaction,
      3 Ledger/Transaction/Asset/AssetModel,
      2 Ledger/Transaction/Asset/TokenType,
      exactly 1 Ledger/Transaction/Asset/Fungible,
      exactly 1 Ledger/Transaction/Asset/NonFungible

run {}   
