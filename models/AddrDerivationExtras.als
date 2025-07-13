module AddrDerivationExtras

open DLTTypes   // brings in PublicKey, DLTAddress, AddrDerivation, etc.

// ————————————————————————————————————————————————————————
// Injectivity and totality for address derivation
// ————————————————————————————————————————————————————————

/**
 * Ensures every public key maps to exactly one address
 * in at least one AddrDerivation instance.
 */
fact PublicKeyDerivesExactlyOneAddr {
  all pk: PublicKey |
    // for each public key, there exists exactly one AddrDerivation
    // where hashes[pk] is defined (not none)
    one ad: AddrDerivation | ad.hashes[pk] != none
}

/**
 * Ensures the address-derivation function is injective:
 * within any AddrDerivation, two different public keys
 * cannot map to the same address.
 */
fact AddressInjectiveWithinScope {
  all disj pk1, pk2: PublicKey, ad: AddrDerivation |
    ad.hashes[pk1] = ad.hashes[pk2] implies pk1 = pk2
}
