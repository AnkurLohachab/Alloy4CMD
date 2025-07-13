module Governance

open User               // brings in DLTUser
open util/integer       // for Int, #, ≥, ≤, sum

// ————————————————————————————————————————————————————————
// 1. Off‐chain governance committee
// ————————————————————————————————————————————————————————

/**
 * The off‐chain committee responsible for governance.
 * Contains one or more DLTUsers as members.
 */
one sig GovCommittee {
  members: some DLTUser    // committee membership set (non‐empty)
}

/**
 * Predicate to check whether a user is authorized
 * (i.e., is a committee member).
 */
pred isAuthorized[u: DLTUser] {
  u in GovCommittee.members
}


// ————————————————————————————————————————————————————————
// 2. Proposal definition and lifecycle
// ————————————————————————————————————————————————————————

/**
 * Enumeration of possible proposal states.
 */
abstract sig ProposalState {}
one sig Pending, Active, Passed, Rejected, Executed extends ProposalState {}

/**
 * Whether a proposal’s voting is open to all or restricted.
 */
enum Participation { Public, Private }

/**
 * Governance proposal record:
 * - id: unique integer identifier
 * - proposer: DLTUser who created it (must be authorized)
 * - createdAt: timestamp of creation
 * - votingStart: timestamp when voting opens
 * - votingEnd: timestamp when voting closes
 * - participation: Public or Private voting
 * - state: current lifecycle state (Pending initially)
 */
sig Proposal {
  id            : one Int,
  proposer      : one DLTUser,
  createdAt     : one Int,
  votingStart   : one Int,
  votingEnd     : one Int,
  participation : one Participation,
  var state     : one ProposalState
}

/**
 * Only committee members may create proposals.
 */
fact OnlyAuthorizedProposers {
  all p: Proposal | p.proposer in GovCommittee.members
}

/**
 * Timestamps must satisfy:
 * createdAt ≤ votingStart < votingEnd.
 */
fact ProposalTimestamps {
  all p: Proposal |
    p.createdAt <= p.votingStart and p.votingStart < p.votingEnd
}

/**
 * Every new proposal begins in the Pending state.
 */
fact InitialProposalState {
  all p: Proposal | p.state = Pending
}


// ————————————————————————————————————————————————————————
// 3. Voting records and constraints
// ————————————————————————————————————————————————————————

/**
 * Possible vote choices.
 */
enum VoteChoice { For, Against, Abstain }

/**
 * A vote cast by a DLTUser on a proposal:
 * - voter: the user casting the vote
 * - proposal: the target proposal
 * - choice: For, Against, or Abstain
 * - at: timestamp of the vote
 */
sig Vote {
  voter    : one DLTUser,
  proposal : one Proposal,
  choice   : one VoteChoice,
  at       : one Int
}

/**
 * Each member may vote at most once per proposal.
 */
fact OneVotePerMember {
  all v1, v2: Vote |
    v1.voter = v2.voter && v1.proposal = v2.proposal implies v1 = v2
}

/**
 * Votes must occur within the proposal’s voting window.
 */
fact VoteWithinWindow {
  all v: Vote |
    v.at >= v.proposal.votingStart and v.at <= v.proposal.votingEnd
}

/**
 * If voting is private, only committee members may vote.
 */
fact PrivateVotingOnlyCommittee {
  all v: Vote |
    v.proposal.participation = Private implies
      v.voter in GovCommittee.members
}


// ————————————————————————————————————————————————————————
// 4. Counting votes and quorum
// ————————————————————————————————————————————————————————

/**
 * Helper: votes of type For on a proposal.
 */
fun votesFor[p: Proposal]:     set Vote { For.~choice & p.~proposal }

/**
 * Helper: votes of type Against on a proposal.
 */
fun votesAgainst[p: Proposal]: set Vote { Against.~choice & p.~proposal }

/**
 * Helper: votes of type Abstain on a proposal.
 */
fun votesAbstain[p: Proposal]: set Vote { Abstain.~choice & p.~proposal }

/**
 * Total votes cast on a proposal.
 */
fun totalVotes[p: Proposal]: set Vote {
  votesFor[p] + votesAgainst[p] + votesAbstain[p]
}

/**
 * Governance parameters including required quorum.
 */
one sig GovParams {
  quorum: one Int   // minimum number of votes needed
}

/**
 * Quorum must be at least 1.
 */
fact QuorumPositive {
  GovParams.quorum >= 1
}

/**
 * If quorum reached and For ≥ Against, proposal passes.
 */
fact DeterminePass {
  all p: Proposal |
    (some params: GovParams |
       #totalVotes[p] >= params.quorum &&
       #votesFor[p]   >= #votesAgainst[p])
    implies p.state = Passed
}

/**
 * If quorum reached and For < Against, proposal is rejected.
 */
fact DetermineReject {
  all p: Proposal |
    (some params: GovParams |
       #totalVotes[p] >= params.quorum &&
       #votesFor[p]   <  #votesAgainst[p])
    implies p.state = Rejected
}


// ————————————————————————————————————————————————————————
// 5. Execution of passed proposals
// ————————————————————————————————————————————————————————

/**
 * A proposal may only be executed if it has passed.
 */
fact ExecutionRules {
  all p: Proposal |
    p.state = Executed implies p.state = Passed
}

/**
 * Transition to execute a proposal.
 */
pred execute[p: Proposal] {
  p.state = Passed
  // optionally: set p.state’ = Executed in next state
}


// ————————————————————————————————————————————————————————
// 6. Temporal constraints 
// ————————————————————————————————————————————————————————

/**
 * Lifecycle progression:
 * - Pending until Active.
// - Active until Passed or Rejected.
 */
fact StateProgression {
  always (all p: Proposal |
    (p.state = Pending) until (p.state = Active) and
    (p.state = Active) until (p.state = Passed or p.state = Rejected)
  )
}

/**
 * Every proposal eventually becomes Active.
 */
fact EventualActivation {
  always (all p: Proposal |
    eventually (p.state = Active)
  )
}


/**
 * Instantiate a small governance trace to validate properties.
 */
run {}   
