module Wallet

open DLTTypes
open User    // brings in DLTUser, ExternalUser, State, First, etc.

// ————————————————————————————————————————————————————————
// 1. Wallets, Keys & Accounts (requirements c.1–c.10)
// ————————————————————————————————————————————————————————

/**
 * Associates a ledger user with exactly one keypair and one on-chain account.
 */
sig DLTUserWallet {
  owner   : one DLTUser,    // who controls this wallet
  kp      : one KeyPair,    // exactly one cryptographic keypair per wallet
  account : one DLTAccount  // exactly one on-chain account per wallet
}

/**
 * Metadata classifying each wallet by connectivity and custody.
 */
sig WalletMeta {
  wallet      : one DLTUserWallet,  // the wallet being described
  connType    : one ConnType,       // c.9: Hot vs. Cold connectivity
  custodyType : one CustodyType     // c.10: Custodial vs. Non-Custodial
}

// ————————————————————————————————————————————————————————
// 2. Connectivity & Custody Types
// ————————————————————————————————————————————————————————

abstract sig ConnType {}             // supertype for connection categories
one sig Hot, Cold extends ConnType {}  // online vs. offline wallets

abstract sig CustodyType {}            // supertype for custody categories
one sig Custodial, NonCustodial extends CustodyType {}  // third-party vs. self-custody

// ————————————————————————————————————————————————————————
// 3. c.1–c.2: KeyPair uniqueness
// Ensures no two distinct KeyPairs share either key.
// ————————————————————————————————————————————————————————
fact KeyPairUniqueness {
  all k1, k2: KeyPair | k1 != k2 implies
    k1.publicKey  != k2.publicKey &&
    k1.privateKey != k2.privateKey
}

// ————————————————————————————————————————————————————————
// 4. c.3–c.4: Key usage
// Ensures every PublicKey and PrivateKey appears in exactly one KeyPair.
// ————————————————————————————————————————————————————————
fact KeysAreUsed {
  all pk: PublicKey  | one kp: KeyPair | kp.publicKey  = pk
  all sk: PrivateKey | one kp: KeyPair | kp.privateKey = sk
}

// ————————————————————————————————————————————————————————
// 5. Helper: derive address from a public key
// ————————————————————————————————————————————————————————
/**
 * Returns the on-chain address derived from hashing the public key.
 */
fun addrOf(pub: PublicKey): one DLTAddress {
  pub.(AddrDerivation.hashes)
}

// ————————————————————————————————————————————————————————
// 6. c.5–c.7: Account linkage & asset constraint
// - Account ID must match the derived address.
// - Account must hold at least one asset.
// ————————————————————————————————————————————————————————
fact AccountLinkageAndAssets {
  all w: DLTUserWallet | {
    // c.6: link account identifier to the derived address
    w.account.identifiedBy = addrOf[w.kp.publicKey]
    // c.7: ensure the account has at least one asset
    some w.account.asset
  }
}

// ————————————————————————————————————————————————————————
// 7. c.8: Distinct wallets ⇒ distinct accounts
// ————————————————————————————————————————————————————————
fact DistinctWalletAccounts {
  all w1, w2: DLTUserWallet | w1 != w2 implies
    w1.account != w2.account
}

// ————————————————————————————————————————————————————————
// 8. c.9: Every wallet has exactly one metadata entry
// ————————————————————————————————————————————————————————
fact MetaExistence {
  all w: DLTUserWallet | one m: WalletMeta | m.wallet = w
}

// ————————————————————————————————————————————————————————
// 9. c.10: Metadata completeness
// Ensures connType and custodyType fields cover only defined partitions.
// ————————————————————————————————————————————————————————
fact MetadataTotality {
  all m: WalletMeta |
    m.connType    in ConnType    &&
    m.custodyType in CustodyType
}

// ————————————————————————————————————————————————————————
// 10. predicates for explicit partition checks
// ————————————————————————————————————————————————————————

/**
 * Partition wallets into Hot vs. Cold sets.
 */
pred defineConnectivityPartitions {
  all m: WalletMeta |
    (m.connType = Hot  or m.connType = Cold)
    // uncomment if you have sets W_hot and W_cold:
    // && (m.connType = Hot  implies m.wallet in W_hot)
    // && (m.connType = Cold implies m.wallet in W_cold)
}

/**
 * Partition wallets into Custodial vs. NonCustodial sets.
 */
pred defineCustodyPartitions {
  all m: WalletMeta |
    (m.custodyType = Custodial     or m.custodyType = NonCustodial)
    // && (m.custodyType = Custodial    implies m.wallet in W_cust)
    // && (m.custodyType = NonCustodial implies m.wallet in W_noncust)
}


run { defineConnectivityPartitions and defineCustodyPartitions } for
  5 DLTUserWallet, 5 WalletMeta,
  5 KeyPair, 5 PublicKey, 5 PrivateKey,
  5 DLTAccount, 5 Asset, 5 DLTAddress,
  5 AddrDerivation, 5 Time,
  5 DLTTypes/User, 5 DLTTypes/Service,
  5 User/DLTUser, 5 User/ExternalUser,
  5 User/State, 1 User/First
