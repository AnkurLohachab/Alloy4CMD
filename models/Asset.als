module Asset

open util/integer       // for Int, +, <
open DLTTypes           // brings in: User, Service, Asset, DLTAccount, DLTAddress, PublicKey, PrivateKey, KeyPair, AddrDerivation, Time
open User               // brings in: DLTUser, ExternalUser

// ————————————————————————————————————————————————————————
//  Asset instances (requirements d.1–d.7)
// ————————————————————————————————————————————————————————

/**
 * On-chain asset, owned by exactly one DLTUser,
 * classified by a TokenType, and carrying an integer value.
 */
sig AssetModel extends Asset {
  owner   : one DLTUser,  // d.1: exactly one owner per asset
  ttype   : one TokenType,  
  unitVal : one Int       // numeric value from V_asset
}

// d.4: fungible vs. non-fungible type hierarchy
abstract sig TokenType {}
one sig Fungible, NonFungible extends TokenType {}  // d.4

// ————————————————————————————————————————————————————————
// d.1–d.3: ownership constraints
// ————————————————————————————————————————————————————————

/**
 * d.2: Ensures no asset is owned by two different users.
 */
fact UniqueOwnership {
  all disj a: AssetModel, u1, u2: DLTUser |
    a.owner = u1 implies u2 != u1
}

/**
 * d.3: Ensures each asset has at least one owner (non-empty).
 */
fact SomeOwner {
  all a: AssetModel | some a.owner
}

// ————————————————————————————————————————————————————————
// d.4: type partitioning
// ————————————————————————————————————————————————————————

/**
 * d.4: Every asset’s type is either Fungible or NonFungible.
 */
fact AssetPartition {
  all a: AssetModel | a.ttype = Fungible or a.ttype = NonFungible
}

// ————————————————————————————————————————————————————————
// d.5: fungible assets share identical unitVal
// ————————————————————————————————————————————————————————

/**
 * d.5: All distinct fungible assets must have equal unitVal.
 */
fact FungibleValueEquality {
  all disj a, b: AssetModel |
    a.ttype = Fungible && b.ttype = Fungible
      implies a.unitVal = b.unitVal
}

// ————————————————————————————————————————————————————————
// d.6: distinct non-fungibles have distinct unitVal
// ————————————————————————————————————————————————————————

/**
 * d.6: All distinct non-fungible assets must have different unitVal.
 */
fact NonFungibleDistinct {
  all disj a, b: AssetModel |
    a.ttype = NonFungible && b.ttype = NonFungible
      implies a.unitVal != b.unitVal
}

// ————————————————————————————————————————————————————————
// d.7: summing two fungible values yields strictly larger value
// ————————————————————————————————————————————————————————

/**
 * d.7: If c is the sum of two fungible assets a and b,
 * then c’s value must be strictly greater than each summand.
 */
fact ValueOrdering {
  all a, b, c: AssetModel |
    a.ttype = Fungible && b.ttype = Fungible && c.ttype = Fungible &&
    a.unitVal + b.unitVal = c.unitVal
      implies a.unitVal < c.unitVal && b.unitVal < c.unitVal
}



run {} for
  5 AssetModel,
  5 DLTUser,           // from User.als
  5 ExternalUser,      // from User.als
  5 DLTTypes/User,     // abstract User
  5 DLTTypes/Service,  // abstract Service
  5 DLTTypes/Asset,    // abstract Asset
  5 DLTTypes/DLTAccount,
  5 DLTTypes/DLTAddress,
  5 DLTTypes/PublicKey,
  5 DLTTypes/PrivateKey,
  5 DLTTypes/KeyPair,
  5 DLTTypes/AddrDerivation,
  5 DLTTypes/Time,
  5 User/State,        // the User module’s State sig
  exactly 1 User/First,// the initial state
  exactly 1 Fungible,
  exactly 1 NonFungible,
  5 Int
