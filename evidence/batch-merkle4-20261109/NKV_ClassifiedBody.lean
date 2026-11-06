import NKV_ReturnBoundary
set_option autoImplicit false
noncomputable section
namespace NKV_ClassifiedBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure NKV_ReturnBoundary

/-- Classification of the direct reference's successful step returns. This is
local symbolic analysis of one iteration/tail, without evaluating a recurrence. -/
theorem no_lost_ok (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (i ai : Indices) (v av : Values)
 (d pos : Usize) :
 NKV_FRef.verifier.candidate.batch_tree_loop.body ops D proof root tree hash
   lo n slot keys i v d pos ≠ ok (.done (ai,av,.Ok (),true)) := by
 intro step
 unfold NKV_FRef.verifier.candidate.batch_tree_loop.body at step
 repeat' first
 | (solve | cases step)
 | uncase_result
 | head_reduce step
 | split at step

set_option pp.proofs false
#print no_lost_ok
#print axioms no_lost_ok
end NKV_ClassifiedBody
end
