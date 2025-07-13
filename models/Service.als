module Service

open DLTTypes
open User

// ————————————————————————————————————————————————————————
// 1. Usable service hierarchy
// ————————————————————————————————————————————————————————

/**
 * Abstract service that can be used by DLTUsers over time.
 * Maps each DLTUser to the set of Timepoints when they use the service.
 */
abstract sig UsableService {
  usedBy: DLTUser -> set Time
}

/**
 * Concrete service types extending UsableService:
 * - DirectService: services invoked directly by users.
 * - OutputService: services that produce outputs for users.
 * - ConsumedService: services whose usage consumes a resource exclusively.
 */
abstract sig DirectService, OutputService, ConsumedService extends UsableService {}


// ————————————————————————————————————————————————————————
// 2. Requirements b.1–b.3
// ————————————————————————————————————————————————————————

/**
 * requirement b.1:
 * Ensures service usage is Boolean: for any service, user, and time,
 * the timepoint is either included in usedBy[u] or not.
 */
assert ServiceUsageBoolean {
  all s: UsableService, u: DLTUser, t: Time |
    t in s.usedBy[u] or t not in s.usedBy[u]
}

// Run the check for a limited scope of model elements
check ServiceUsageBoolean for 
  exactly 3 UsableService, 
  exactly 2 DirectService, 
  exactly 2 OutputService, 
  exactly 2 ConsumedService, 
  exactly 3 DLTUser, 
  exactly 3 ExternalUser,
  exactly 3 Time, 
  exactly 3 User, 
  exactly 3 Service, 
  exactly 3 Asset, 
  exactly 3 DLTAccount, 
  exactly 3 DLTAddress, 
  exactly 3 KeyPair, 
  exactly 3 PublicKey, 
  exactly 3 PrivateKey, 
  exactly 3 State, 
  exactly 1 First, 
  exactly 1 AddrDerivation 

/**
 * requirement b.2:
 * DirectService and OutputService usages cannot overlap
 * for the same user at the same timepoint.
 */
fact DirectOutputNoOverlap {
  all ds: DirectService, os: OutputService, u: DLTUser, t: Time |
    t in ds.usedBy[u] implies t not in os.usedBy[u]
}

/**
 * requirement b.3:
 * A ConsumedService can be used by at most one user at any given timepoint.
 */
fact UniqueConsumedService {
  all cs: ConsumedService, u1, u2: DLTUser, t: Time |
    t in cs.usedBy[u1] and u1 != u2 implies t not in cs.usedBy[u2]
}
