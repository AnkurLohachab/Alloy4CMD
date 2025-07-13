module DLTTypes

// ————————————————————————————————————————————————————————
// Basic Entities
// ————————————————————————————————————————————————————————

/**
 * Abstract representation of any actor on the ledger,
 * whether a human user or an automated system component.
 */
abstract sig User {}

/**
 * Abstract notion of a service interacting with the ledger,
 * e.g., an exchange, oracle, or identity provider.
 */
abstract sig Service {}

/**
 * Anything of value tracked on-chain, whether fungible tokens
 * or unique non-fungible items.
 */
abstract sig Asset {}

/**
 * On-chain account holding assets and identified by an address.
 */
sig DLTAccount {
  asset       : set Asset,         // the set of assets owned by this account
  identifiedBy: lone DLTAddress    // optional address identifying this account
}

/**
 * Blockchain address, typically a 160-bit value in real systems.
 */
sig DLTAddress {}


// ————————————————————————————————————————————————————————
// Key Pairs
// ————————————————————————————————————————————————————————

/**
 * Public key used to verify signatures.
 */
sig PublicKey {}

/**
 * Private key used to create signatures.
 */
sig PrivateKey {}

/**
 * Associates a public key with its corresponding private key.
 */
sig KeyPair {
  publicKey : one PublicKey,     // the public half of the keypair
  privateKey: one PrivateKey     // the private half of the keypair
}


// ————————————————————————————————————————————————————————
// Address-Derivation Map
// ————————————————————————————————————————————————————————

/**
 * Mapping from each PublicKey to the on-chain address
 * derived via its hash function.
 */
sig AddrDerivation {
  hashes: PublicKey -> one DLTAddress   // function: pubKey ↦ address
}


// ————————————————————————————————————————————————————————
// Time
// ————————————————————————————————————————————————————————

/**
 * Abstract timepoint, for timestamping or ordering events.
 */
sig Time {}
