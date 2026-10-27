import JGo_TX2_WeightPoints
import JGo_TX2_WeightPointTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_StatementPoints
open Aeneas Aeneas.Std Result FIn_WeightsExtract JGo_TX2_WeightData
attribute [local irreducible] field.QM31.sub

theorem source : state_only_prefix.r0.statement_points alpha=ok points := by
  unfold state_only_prefix.r0.statement_points state_only_prefix.state_only_statement_points
  change (do
    let successor ← state_only_prefix.state_only_statement_points_loop
      ⟨{start:=0#usize,«end»:=10#usize}⟩ alpha alpha field.QM31.ONE
    let a ← field.QM31.sub field.QM31.ONE (alpha.val[7])
    let absorption ← Array.update alpha 7#usize a
    let b ← Array.index_usize absorption 6#usize
    let c ← field.QM31.sub field.QM31.ONE b
    let absorption1 ← Array.update absorption 6#usize c
    ok (Array.make 3#usize [alpha,successor,absorption1]))=ok points
  rw [JGo_TX2_WeightPoints.loop,bind_tc_ok,JGo_TX2_WeightPointTail.sub7,bind_tc_ok,
    JGo_TX2_WeightPointTail.update7,bind_tc_ok]
  have index6 : Array.index_usize JGo_TX2_WeightPointTail.first 6#usize=
    ok (JGo_TX2_WeightPointTail.first.val[6]) := rfl
  rw [index6,bind_tc_ok,JGo_TX2_WeightPointTail.sub6,bind_tc_ok,JGo_TX2_WeightPointTail.update6,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGo_TX2_StatementPoints
end
