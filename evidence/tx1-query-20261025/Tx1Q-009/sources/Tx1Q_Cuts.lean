import Tx1Q_PrefixInstall
import Op4P_Cuts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Cuts
open AspisR1CurrentCaller

/-- Inversion of the existing emitted suffix, not a second successful run. -/
theorem suffix (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (saved : alloc.vec.Vec U8)
    (success : Tx1Reachability.afterPrepare ops D pub proof split hash none p g = ok (.Ok saved)) :
    ∃ (a : verifier.Accumulator) (root : Array U8 32#usize)
      (geo : verifier.QueryGeometry) (b : verifier.BatchedWeights)
      (out : verifier.Accumulator) (after : verifier.BatchedWeights)
      (flushed : Slice aspis_core.field.QM31),
      ops.op20 .S2 = ok (.Ok a) ∧
      ops.op6 D proof p root 0#usize hash = ok (.Ok ()) ∧
      ops.op19 p.queries 0#usize split = ok (.Ok geo) ∧
      ops.op18 a.weights.deref = ok (.Ok b) ∧
      ops.op7 proof p a g none geo b split = ok (.Ok (out,after)) ∧
      ops.op17 after out.weights.deref = ok flushed ∧
      ops.op16 D p {out with weights := ⟨flushed.val,flushed.property⟩} proof pub hash = ok saved := by
  unfold Tx1Reachability.afterPrepare at success
  repeat' first
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals
    have same := core.result.Result.Ok.inj (Result.ok.inj success)
    subst saved
    exact ⟨_,_,_,_,_,_,_,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption,by assumption⟩

#print axioms suffix
end AspisR1.Tx1Q_Cuts
end
