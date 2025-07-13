module FeeMarket

open Transaction          // brings in Transaction, TransferPayload, payload, sender
open Ledger               // brings in BlockRec, data: set Transaction
open Asset                // brings in Token
open User                 // brings in DLTUser
open util/integer         // for Int, +, *, ≥, sum

// ————————————————————————————————————————————————————————
// 1. Dedicated gas token
// ————————————————————————————————————————————————————————

/**
 * GasToken is a example on-chain token used to pay transaction fees.
 */
sig GasToken extends Token {}


// ————————————————————————————————————————————————————————
// 2. On-chain record of gas usage & price
// ————————————————————————————————————————————————————————

/**
 * Records gas metrics for a transaction:
 * - tx: the transaction in question.
// - gasUsed: units of gas consumed.
// - gasPrice: price per gas unit.
// - fee: total fee paid (gasUsed * gasPrice).
 */
sig GasRecord {
  tx:       one Transaction,
  gasUsed:  one Int,
  gasPrice: one Int,
  fee:      one Int
}


// ————————————————————————————————————————————————————————
// 3. Off-chain fee object linking record to payer
// ————————————————————————————————————————————————————————

/**
 * Associates a GasRecord with the paying user.
 */
sig TxFee {
  record: one GasRecord,
  payer:  one DLTUser
}


// ————————————————————————————————————————————————————————
// 4. GasRecord fields non-negative
// ————————————————————————————————————————————————————————

/**
 * Ensures gas metrics and fee are not negative.
 */
fact GasRecordNonNegative {
  all gr: GasRecord |
    gr.gasUsed  >= Int[0] and
    gr.gasPrice >= Int[0] and
    gr.fee      >= Int[0]
}


// ————————————————————————————————————————————————————————
// 5. Fee computation: fee = gasUsed * gasPrice
// ————————————————————————————————————————————————————————

/**
 * Computes fee as the product of gasUsed and gasPrice.
 */
fact ComputeGasFee {
  all gr: GasRecord |
    gr.fee = mul[gr.gasUsed, gr.gasPrice]
}


// ————————————————————————————————————————————————————————
// 6. Fee-payer must match transaction sender
// ————————————————————————————————————————————————————————

/**
 * Ensures that the user paying the fee is the sender of the transaction.
 */
fact FeePayerMatches {
  all tf: TxFee |
    tf.payer = tf.record.tx.payload.sender
}


// ————————————————————————————————————————————————————————
// 7a. Every GasRecord’s transaction appears in some block
// ————————————————————————————————————————————————————————

/**
 * Each GasRecord must reference a transaction included in the ledger.
 */
fact GasRecordTxInBlock {
  all gr: GasRecord |
    some b: BlockRec | gr.tx in b.data
}


// ————————————————————————————————————————————————————————
// 7b. Every TxFee’s transaction appears in some block
// ————————————————————————————————————————————————————————

/**
 * Each TxFee must reference a GasRecord whose transaction is on-chain.
 */
fact TxFeeTxInBlock {
  all tf: TxFee |
    some b: BlockRec | tf.record.tx in b.data
}


// ————————————————————————————————————————————————————————
// 8. Global gas parameters
// ————————————————————————————————————————————————————————

/**
 * Global parameters for the gas market:
 * - baseFee: protocol-specified minimum fee.
// - gasLimitPerBlock: maximum gas units allowed per block.
 */
one sig GasParams {
  baseFee:          one Int,
  gasLimitPerBlock: one Int
}

/**
 * Ensures gas parameters are strictly positive.
 */
fact GasParamsPositive {
  all p: GasParams |
    p.baseFee > Int[0] and p.gasLimitPerBlock > Int[0]
}


// ————————————————————————————————————————————————————————
// 9. Block gas-limit enforcement
// ————————————————————————————————————————————————————————

/**
 * Calculates total gas used by all transactions in a block.
 */
fun blockGasUsed[b: BlockRec]: one Int {
  sum[(b.data.~tx).gasUsed]
}

/**
 * Ensures no block exceeds the configured gas limit.
 */
fact BlockGasLimit {
  all b: BlockRec |
    blockGasUsed[b] <= GasParams.gasLimitPerBlock
}


run {} 
