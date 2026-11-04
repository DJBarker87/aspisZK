import NFQ_STAGE2_IMPORT
import Lean
open Lean Elab Command
run_cmd do
  for (n, _) in (← getEnv).constants.toList do
    let s := n.toString
    if s.endsWith ".CM31.square" || s.endsWith ".CM31.write_le_bytes" || s.endsWith ".QM31.write_le_bytes" || s.endsWith ".WideExact.new" || s.endsWith ".WideExact.neg" || s.endsWith ".qm31_pack_base4" || ("generated_".isInfixOf s) && s.endsWith "mul_eq_probe" then
      logInfo s
#print AspisR1CurrentWide.field.wide_exact.WideExact.new
#print AspisR1CurrentWide.field.wide_exact.WideExact.neg
