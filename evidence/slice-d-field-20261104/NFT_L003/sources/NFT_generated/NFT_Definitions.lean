import NFQ_STAGE2_IMPORT
import Lean
open Lean Elab Command
run_cmd do
  for (n, _) in (← getEnv).constants.toList do
    let s := n.toString
    if s.startsWith "AspisR1CurrentWide.field.wide_exact" || s.startsWith "AspisR1CurrentWide.Proof.current" || s.endsWith ".current_neg_mod" then
      logInfo s
#print OraclePortCkptAbi2Extracted.aspis_core.field.CM31.write_le_bytes
#print OraclePortCkptAbi2Extracted.aspis_core.field.QM31.write_le_bytes
#print AspisR1SelectedMaskProbe.field.CM31.square
#print FIq_Native.field.CM31.square
#print AspisR1Post25Sampler.field.WideExact.new
#print AspisR1SelectedMaskProbe.field.qm31_pack_base4
