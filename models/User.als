module User

open DLTTypes

//———————————————————————————————————————————————
// 1. Role hierarchy
//———————————————————————————————————————————————

/**
 * On-chain user roles.
 * - DLTUser: participants with ledger accounts.
// - ExternalUser: users outside the ledger context.
 */
sig DLTUser, ExternalUser extends User {}


//———————————————————————————————————————————————
// 2. System states
//———————————————————————————————————————————————

/**
 * Represents a snapshot of the system at a point in time.
 */
sig State {
  next: lone State,        // optional pointer to the next state
  DU:   set DLTUser,       // users already added to on-chain (Direct Users)
  EU:   set ExternalUser   // users yet to be added (External Users)
}

/**
 * The initial state of the system; there is exactly one.
 */
one sig First extends State {}

/**
 * In the initial state, there must be no successor.
 */
fact {
  no First.next
}


//———————————————————————————————————————————————
// 3. User invariants
//———————————————————————————————————————————————

/**
 * requirement a.1:
 * Initially, there must be at least one external user.
 */
fact {
  some First.EU
}

/**
 * requirement a.2:
 * At any state, ExternalUser and DLTUser sets are disjoint.
 */
fact {
  all u: User, s: State |
    u in s.EU implies u not in s.DU
}

/**
 * requirement a.3:
 * At any state, every User is either external or direct.
 */
fact {
  all s: State |
    s.DU + s.EU = User
}


//———————————————————————————————————————————————
// 4. Transition addUser
//———————————————————————————————————————————————

/**
 * requirement a.4:
 * Transition that moves an ExternalUser r from EU to DU.
 *
 * @param r   the ExternalUser to add
 * @param s   the current state
 * @param s2  the next state after adding r
 */
pred addUser[r: ExternalUser, s, s2: State] {
  s.next = s2               // link current state to next
  r in s.EU                  // r must be external in s
  s2.DU = s.DU + r           // add r to direct-user set
  s2.EU = s.EU - r           // remove r from external-user set
}


//———————————————————————————————————————————————
// 5. Invariant and preservation check
//———————————————————————————————————————————————

/**
 * Combined invariant to check at any state.
 * - There is at least one ExternalUser.
// - Disjointness of EU and DU.
// - Partition covers all Users.
 */
pred InvariantPhi[s: State] {
  some s.EU
  all u: User | u in s.EU implies u not in s.DU
  s.DU + s.EU = User
}

/**
 * Assert that executing addUser preserves the invariant.
 */
assert AddPreservesInvariant {
  all r: ExternalUser, s, s2: State |
    InvariantPhi[s] and addUser[r, s, s2]
    implies InvariantPhi[s2]
}

/**
 * Check the preservation assertion.
 */
check AddPreservesInvariant for 5
