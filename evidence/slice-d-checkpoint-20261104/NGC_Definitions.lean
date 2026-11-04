import NFT_STAGE2_IMPORT
import Lean
open Lean Elab Command
run_cmd do
 for (n,_) in (←getEnv).constants.toList do
  let s := n.toString
  if s.endsWith "Accumulator.new" || s.endsWith "BatchedWeights.finish" || s.endsWith "heap.filled" || s.endsWith "SolanaDigest.digest" then
   logInfo s
#print AspisR1Stage2.verifier.Accumulator.new
#print AspisR1Stage2.verifier.BatchedWeights.finish
#print AspisR1.OraclePortStdAllocation.filled
