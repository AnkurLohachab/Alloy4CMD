module SoftwareClients

open DLTTypes        // brings in Time, Service, etc.
open User            // brings in DLTUser, ExternalUser
open Wallet          // brings in DLTUserWallet, WalletMeta
open util/integer    // for Int, >

// ————————————————————————————————————————————————————————
// h.1 Clients = WalletClients ∪ NodeClients
// ————————————————————————————————————————————————————————

/**
 * Abstract superclass for all software clients interacting with the network.
 */
abstract sig Client {}

/**
 * Clients that act on behalf of end-users via wallets.
 * - wallet: the on-chain wallet they control.
// - nodePeers: the set of node-clients they connect to.
 */
sig WalletClient extends Client {
  wallet    : one DLTUserWallet,
  nodePeers : set NodeClient
}

/**
 * Clients that run full node software.
// - roles: protocol roles (execution and/or consensus).
// - disk: storage capacity (TB) as a function of time.
// - netBW: network bandwidth (GB/s) as a function of time.
// - peers: P2P connections to other node-clients.
// - vendor: software vendor implementation.
// - version: software version identifier.
 */
abstract sig NodeClient extends Client {
  roles    : set CRole,
  disk     : Time -> one Int,
  netBW    : Time -> one Int,
  peers    : set NodeClient,
  vendor   : one Vendor,
  version  : one Version
}

// h.1: Partition between wallet-based and node-based clients.
fact ClientPartition {
  WalletClient + NodeClient = Client
}

// Ensure wallet clients peer with at least one node.
fact WalletConnectivity {
  all w: WalletClient | some w.nodePeers
}


// ————————————————————————————————————————————————————————
// h.3 Storage-class partition: light vs. full clients
// ————————————————————————————————————————————————————————

/**
 * Light‐weight node clients with limited storage.
 */
sig LightClient, FullClient extends NodeClient {}

// Partition NodeClient into storage classes.
fact StoragePartition {
  LightClient + FullClient = NodeClient
}


// ————————————————————————————————————————————————————————
// h.2 Protocol roles: execution vs. consensus
// ————————————————————————————————————————————————————————

/**
 * Protocol roles that a node client may perform.
 */
abstract sig CRole {}
one sig Execution, Consensus extends CRole {}

// Every node client must have at least one protocol role.
fact RolesNonEmpty {
  all n: NodeClient | some n.roles
}


// ————————————————————————————————————————————————————————
// h.5 Implementation diversity: vendor & version
// ————————————————————————————————————————————————————————

/**
 * Software vendors providing node-client implementations.
 */
abstract sig Vendor {}
one sig Geth, Besu, Nethermind, Prysm extends Vendor {}

/**
 * Version identifiers for node-client software.
 */
sig Version {}

// Each node client must specify a vendor and a version.
fact VendorVersion {
  all n: NodeClient | some n.vendor and some n.version
}


// ————————————————————————————————————————————————————————
// h.4 Resource usage constraints
// ————————————————————————————————————————————————————————

/**
 * Node-client disk usage must always be positive.
 */
fact PositiveDisk {
  all n: NodeClient, t: Time | n.disk[t] > 0
}

/**
 * Node-client network bandwidth must always be positive.
 */
fact PositiveNetBW {
  all n: NodeClient, t: Time | n.netBW[t] > 0
}

/**
 * Full clients require substantial disk capacity.
 */
fact FullHasHighDisk {
  all n: FullClient, t: Time | n.disk[t] >= 1000
}

/**
 * Light clients have limited disk capacity.
 */
fact LightHasLowDisk {
  all n: LightClient, t: Time | n.disk[t] <= 100
}


// ————————————————————————————————————————————————————————
// P2P-graph properties for node clients
// ————————————————————————————————————————————————————————

/**
 * No client peers with itself.
 */
fact P2PIrreflexive {
  no n: NodeClient | n in n.peers
}

/**
 * Peer connections are bidirectional.
 */
fact P2PSymmetric {
  all n, m: NodeClient | m in n.peers implies n in m.peers
}


/**
 * Instantiate a small network of clients to validate constraints.
 */
run {} for
    5 Int,
    5 Client, 5 WalletClient, 5 NodeClient,
    3 FullClient, 2 LightClient,
    2 CRole, exactly 1 Execution, exactly 1 Consensus,
    5 Time,
    4 Vendor, 5 Version,
    5 Service, 5 Asset,
    5 DLTAccount, 5 DLTAddress,
    5 PublicKey, 5 PrivateKey, 5 KeyPair, 5 AddrDerivation,
    5 DLTUserWallet, 5 DLTUser, 5 ExternalUser,
    5 State, exactly 1 First,
    5 WalletMeta
