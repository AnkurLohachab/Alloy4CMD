module Consensus

open PeerNodes          // brings in PeerNode, FullNode, LightNode, BlockId, etc.
open util/integer       // for Int, +, >

// ————————————————————————————————————————————————————————
// f.6  Consensus values, time, and non‐faulty nodes
// ————————————————————————————————————————————————————————

/**
 * Values over which peers must reach agreement.
 */
sig ConsValue {}            

// We model time directly as Int timestamps.

/**
 * The subset of nodes assumed honest (non‐faulty).
 */
one sig NonFaulty extends PeerNode {}  


// ————————————————————————————————————————————————————————
// f.7  Proposals and Decisions (enhanced)
// ————————————————————————————————————————————————————————

/**
 * A proposal by a non‐faulty node (proposer) for value v at time t.
 */
sig Proposal {
  proposer: one NonFaulty,  // only non‐faulty nodes may propose
  v:        one ConsValue,  // proposed consensus value
  t:        one Int         // proposal timestamp
}

/**
 * A decision by a non‐faulty node (decider) on value v at time t.
 */
sig Decision {
  decider: one NonFaulty,   // node making the decision
  v:       one ConsValue,   // decided value
  t:       one Int          // decision timestamp
}


// ————————————————————————————————————————————————————————
// Extra sanity constraints
// ————————————————————————————————————————————————————————

/**
 * f.7: no non‐faulty node issues more than one proposal.
 */
fact UniqueProposal {
  all p1, p2: Proposal |
    p1.proposer = p2.proposer implies p1 = p2
}

/**
 * Each honest node must issue at least one proposal.
 */
fact ProposerActivity {
  all n: NonFaulty |
    some p: Proposal | p.proposer = n
}

/**
 * All proposals must use the same consensus value.
 */
fact UniformProposal {
  all p1, p2: Proposal |
    p1.v = p2.v
}

/**
 * No node makes more than one decision.
 */
fact UniqueDecisionPerNode {
  all d1, d2: Decision |
    d1.decider = d2.decider implies d1 = d2
}

/**
 * Decisions occur after that node’s own proposal.
 */
fact DecisionAfterProposal {
  all d: Decision |
    some p: Proposal |
      p.proposer = d.decider and d.t > p.t
}


// ————————————————————————————————————————————————————————
// f.8  Termination (liveness): every non‐faulty node decides
// ————————————————————————————————————————————————————————

/**
 * Every honest node eventually makes a decision.
 */
pred Termination {
  all n: NonFaulty |
    some d: Decision | d.decider = n
}


// ————————————————————————————————————————————————————————
// f.9  Validity: decisions follow proposals
// ————————————————————————————————————————————————————————

/**
 * Any decided value must have been proposed.
 */
pred Validity {
  all d: Decision |
    some p: Proposal | p.v = d.v
}


// ————————————————————————————————————————————————————————
// f.10 Agreement (safety): decisions agree
// ————————————————————————————————————————————————————————

/**
 * No two decisions differ in value.
 */
pred Agreement {
  all d1, d2: Decision |
    d1.v = d2.v
}


// ————————————————————————————————————————————————————————
// Top‐level assertion and bounded check
// ————————————————————————————————————————————————————————

/**
 * Combined consensus specification.
 */
assert ConsensusSpec {
  Termination and Validity and Agreement
}

check ConsensusSpec for
    exactly 1 NonFaulty,
    3 PeerNode,
    5 ConsValue,
    5 Proposal,
    5 Decision,
    10 Int,
    5 BlockId
