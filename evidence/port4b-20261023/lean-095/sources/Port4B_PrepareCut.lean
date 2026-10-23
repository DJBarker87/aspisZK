import Port4B_FoldedCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_PrepareCut
open Aeneas Aeneas.Std Result VTop_Stages

theorem branch_pair {G : Type} (r : core.result.Result verifier.Prepared verifier.Error × G)
    (p : verifier.Prepared)
    (branch : core.result.Result.Insts.CoreOpsTry.branch r.1=ok (.Continue p)) : r=(.Ok p,r.2) := by
  rcases r with ⟨r,g⟩
  cases r with
  | Err e => cases branch
  | Ok value =>
    have same := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj branch)
    subst value
    rfl

/-- ONE accepted TX1 supplies the original prepare success, its exact zero
input, the physical folded-root read/copy and the accepted batch0 call. -/
theorem tx1 (base : Ops) {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 (Port4B_FoldedCut.install base)
      D semantic pub proof split hash none=ok (.Ok saved)) :
    ∃ zero g p root view,
      base.op1=ok zero ∧
      base.op7 D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root) ∧
      Port4B_Install.batch D proof p root 0#usize hash=ok (.Ok ()) := by
  unfold verifier.candidate.tx1 at accepted
  simp only [Port4B_FoldedCut.install] at accepted
  repeat' first
  | (solve | cases accepted)
  | rcasesm* (_ × _)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,_,_,_,_,by assumption,by assumption,by assumption,by assumption,by assumption⟩

#print axioms branch_pair
#print axioms tx1
end AspisR1.Port4B_PrepareCut
end
