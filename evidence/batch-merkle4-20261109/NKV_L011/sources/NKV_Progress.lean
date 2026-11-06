import NKV_ClassifiedBody
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace NKV_Progress
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary

theorem continues (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (i ai : Indices) (v av : Values)
 (d pos ad apos : Usize)
 (step : NKV_FRef.verifier.candidate.batch_tree_loop.body ops D proof root tree hash
   lo n slot keys i v d pos=ok (.cont (ai,av,ad,apos))) :
 apos=Usize.wrapping_add pos 1#usize ∧ pos<n := by
 unfold NKV_FRef.verifier.candidate.batch_tree_loop.body at step
 repeat' first
 | (solve | cases step)
 | uncase_result
 | head_reduce step
 | split at step
 all_goals cases Result.ok.inj step;exact ⟨rfl,by assumption⟩

/-- The direct reference never loses a successful return at its boundary. -/
theorem done_classified (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (i : Indices) (v : Values)
 (d pos : Usize) (out : Out)
 (step : NKV_FRef.verifier.candidate.batch_tree_loop.body ops D proof root tree hash
   lo n slot keys i v d pos=ok (.done out)) : WellClassified out := by
 rcases out with ⟨ai,av,r,b⟩
 intro lost success
 cases b with
 | false => cases lost
 | true =>
   change r=.Ok () at success
   rw [success] at step
   exact NKV_ClassifiedBody.no_lost_ok ops D proof root tree hash lo n slot keys i ai v av d pos step

set_option pp.proofs false
#print continues
#print done_classified
#print axioms continues
#print axioms done_classified
end NKV_Progress
end
