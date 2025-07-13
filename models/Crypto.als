module Crypto

open DLTTypes        // brings in PublicKey, PrivateKey, KeyPair, DLTAddress, AddrDerivation
open util/boolean    // for Bool, True, False

// ————————————————————————————————————————————————
// 1. Basic atoms
// ————————————————————————————————————————————————

/**
 * Abstract representation of a message (e.g., a byte sequence).
 */
sig Message {}

/**
 * Placeholder for a 256-bit digest produced by hash or MAC functions.
 */
sig Hash {}


// ————————————————————————————————————————————————
// 2. Symmetric encryption
// ————————————————————————————————————————————————

/**
 * Shared symmetric key for encryption/decryption.
 */
sig SymKey {}

/**
 * Ciphertext produced by symmetric encryption.
 */
sig Cipher {}

/**
 * Symmetric encryption algorithm:
 * enc[k][m] returns the ciphertext of message m under key k.
 */
sig SymEnc {
  enc: SymKey -> Message -> one Cipher
}

/**
 * Symmetric decryption algorithm:
 * dec[k][c] returns the plaintext message from ciphertext c under key k.
 */
sig SymDec {
  dec: SymKey -> Cipher -> one Message
}

/**
 * f.2.1: Perfect correctness of symmetric encryption:
 * decrypting an encrypted message yields the original message.
 */
fact Symmetry {
  all se: SymEnc, sd: SymDec, k: SymKey, m: Message |
    sd.dec[k][ se.enc[k][m] ] = m
}

/**
 * f.2.2: Cipher injectivity:
 * under the same key, two different messages never map to the same cipher.
 */
fact NoCipherCollision {
  all se: SymEnc, k: SymKey, m1, m2: Message |
    se.enc[k][m1] = se.enc[k][m2] implies m1 = m2
}


// ————————————————————————————————————————————————
// 3. Message Authentication Codes (MACs)
// ————————————————————————————————————————————————

/**
 * Abstract MAC algorithm:
 * mac[k][m] produces a hash tag authenticating message m under key k.
 */
sig MACAlg {
  mac: SymKey -> Message -> one Hash
}

/**
 * f.3: MAC totality:
 * every MAC algorithm must produce some hash for each (key, message) pair.
 */
fact MACTotal {
  all a: MACAlg, k: SymKey, m: Message |
    some a.mac[k][m]
}


// ————————————————————————————————————————————————
// 4. Random-oracle hashing
// ————————————————————————————————————————————————

/**
 * Random-oracle abstraction:
 * h[m] returns a unique hash for message m.
 */
sig RO {
  h: Message -> one Hash
} {
  // Enforce injectivity within the finite model
  all disj m1, m2: Message | h[m1] = h[m2] implies m1 = m2
}


// ————————————————————————————————————————————————
// 5. Asymmetric signatures
// ————————————————————————————————————————————————

/**
 * A digital signature, binding a message hash to a public key.
 */
sig Signature {
  msg : one Hash,        // the hashed message being signed
  key : one PublicKey    // the public key corresponding to the signer
}

/**
 * Abstract signature algorithm:
 * sign[sk][h] produces a signature under private key sk on hash h.
 */
sig SignAlg {
  sign: PrivateKey -> Hash -> one Signature
}

/**
 * f.5.1: Signing correctness:
 * signing a hash under a keypair’s private key yields a signature
 * whose key and msg fields match the public key and input hash.
 */
fact SignCorrectness {
  all sa: SignAlg, kp: KeyPair, m: Message |
    let hval = RO.h[m],
        s    = sa.sign[kp.privateKey][hval] |
      s.msg = hval and s.key = kp.publicKey
}

/**
 * f.5.2: Signature uniqueness:
 * no two distinct Signature atoms carry the same (key, msg) pair.
 */
fact SignatureUniqueness {
  all disj s1, s2: Signature |
    s1.key = s2.key and s1.msg = s2.msg implies s1 = s2
}


// ————————————————————————————————————————————————
// 6. Sanity-check: coherence of all primitives
// ————————————————————————————————————————————————

/**
 * Combined assertion ensuring encryption, MACs, and signatures behave correctly.
 */
assert CryptoCoherence {
  // 6.1: Signing correctness
  all sa: SignAlg, kp: KeyPair, m: Message |
    let hval = RO.h[m],
        s    = sa.sign[kp.privateKey][hval] |
      s.key = kp.publicKey and s.msg = hval

  // 6.2: Encryption/decryption round-trip
  all se: SymEnc, sd: SymDec, k: SymKey, m: Message |
    sd.dec[k][ se.enc[k][m] ] = m

  // 6.3: MAC availability
  all ma: MACAlg, k: SymKey, m: Message |
    some ma.mac[k][m]
}

/**
 * Bounded check of the CryptoCoherence assertion.
 */
check CryptoCoherence for
  1 Message, 1 Hash,
  3 SymKey, 3 Cipher,
  2 SymEnc, 2 SymDec,
  2 MACAlg,
  2 RO,
  2 SignAlg,
  3 Signature,
  3 DLTAccount, 3 DLTAddress, 3 AddrDerivation,
  3 Time,
  3 User, 3 Service, 3 Asset,
  exactly 3 PublicKey, 3 PrivateKey, 3 KeyPair
