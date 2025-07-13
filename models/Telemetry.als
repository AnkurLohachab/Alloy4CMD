module Telemetry

open Consensus               // brings in Proposal, Decision, and their .v and .t fields
open util/integer            // for Int, <, ≤, sum, max, div

// ————————————————————————————————————————————————————————
// 1. Telemetry Tracking
// ————————————————————————————————————————————————————————

/**
 * Captures the latency between a proposal and its corresponding decision.
 * - prop: the Proposal instance
 * - dec:  the matching Decision instance
 * - ms:   the observed latency in milliseconds
 */
sig Latency {
  prop : one Proposal,
  dec  : one Decision,
  ms   : one Int
}

/**
 * Ensures each Latency entry links a proposal and decision on the same value.
 */
fact LatencyBinding {
  all l: Latency |
    l.prop.v = l.dec.v
}


// ————————————————————————————————————————————————————————
// 2. Basic SLO Assertion
//     (Example: finality within 5 seconds)
// ————————————————————————————————————————————————————————

/**
 * Service‐level objective: all observed latencies must be under 5000 ms.
 */
assert FiveSecondFinality {
  all l: Latency | l.ms < 5000
}

/**
 * Check the FiveSecondFinality assertion 
 */
check FiveSecondFinality 


// ————————————————————————————————————————————————————————
// 3. Worst‐Case and Average Latency
// ————————————————————————————————————————————————————————

/**
 * Collects all latency measurements.
 */
fun allLatencies: set Int {
  Latency.ms
}

/**
 * Computes the worst‐case latency.
 */
fun maxLatency: one Int {
  max[ allLatencies ]
}

/**
 * Computes the average latency (integer division).
 */
fun avgLatency: one Int {
  div[ sum[ allLatencies ], #Latency ]
}

/**
 * Assert that the maximum observed latency stays below 8000 ms.
 */
assert MaxLatencyBelowThreshold {
  maxLatency < 8000
}
check MaxLatencyBelowThreshold

/**
 * Assert that the average latency stays below 3000 ms.
 */
assert AverageLatencyAcceptable {
  avgLatency < 3000
}
check AverageLatencyAcceptable 


// ————————————————————————————————————————————————————————
// 4. Optional Temporal Diagnosis (Alloy 6 LTL)
// ————————————————————————————————————————————————————————

/**
 * Predicate: once a proposal exists, its matching decision
 * must eventually occur.
 */
pred DecisionFollowsProposal[l: Latency] {
  always (l.prop in Proposal implies eventually (l.dec in Decision))
}

/**
 * Assert temporal consistency across latency entries.
 */
assert TemporalConsistency {
  all l: Latency | DecisionFollowsProposal[l]
}
check TemporalConsistency 
