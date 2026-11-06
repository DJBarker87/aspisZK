import NKV_OuterSource
set_option autoImplicit false
noncomputable section
namespace NKV_OkTransport
open Aeneas Aeneas.Std Result AspisR1Stage2
open NKV_StepErasure
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem tree_observation (m : Result (Reply × Indices × Values)) (idx : Indices) (val : Values) :
 NKV_ReturnBoundary.reject m=ok ((),idx,val) ↔ m=ok (.Ok (),idx,val) := by
 cases m with
 | fail e => simp only [NKV_ReturnBoundary.reject,reduceCtorEq]
 | div => simp only [NKV_ReturnBoundary.reject,reduceCtorEq]
 | ok out =>
   rcases out with ⟨r,i,v⟩
   cases r with
   | Err e => simp only [NKV_ReturnBoundary.reject,reduceCtorEq]
   | Ok u => cases u;rfl

theorem parent_observation (m : Result Reply) :
 NKV_ParentSource.observe m=ok () ↔ m=ok (.Ok ()) := by
 cases m with
 | fail e => simp only [NKV_ParentSource.observe,reduceCtorEq]
 | div => simp only [NKV_ParentSource.observe,reduceCtorEq]
 | ok r => cases r with
   | Err e => simp only [NKV_ParentSource.observe,reduceCtorEq]
   | Ok u => cases u;rfl

/-- Full value equality on Ok, including BOTH complete mutable arrays. -/
theorem tree (H : Bytes → HashState) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Array U8 32#usize) (batch kind : Usize) (bound : batch.val<2)
 (idx outIdx : Indices) (val outVal : Values) :
 AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ()=ok (.Ok (),outIdx,outVal) ↔
 NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val ()=ok (.Ok (),outIdx,outVal) := by
 rw [←tree_observation,←tree_observation,NKV_ConcreteChildren.source H proof raw root batch kind bound idx val]

theorem values (H : Bytes → HashState) (proof : Slice U8) (raw : Array U32 22#usize)
 (roots : Array (Array U8 32#usize) 3#usize) (batch : Usize) (bound : batch.val<2) :
 AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw roots batch ()=ok (.Ok ()) ↔
 NKV_FRef.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw roots batch ()=ok (.Ok ()) := by
 rw [←parent_observation,←parent_observation,NKV_OuterSource.values_concrete H proof raw roots batch bound]

theorem batch (H : Bytes → HashState) (proof : Slice U8) (p : verifier.Prepared)
 (folded : Array U8 32#usize) (batch : Usize) (bound : batch.val<2) :
 AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof p folded batch ()=ok (.Ok ()) ↔
 NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof p folded batch ()=ok (.Ok ()) := by
 rw [←parent_observation,←parent_observation,NKV_OuterSource.concrete H proof p folded batch bound]

set_option pp.proofs false
#print tree
#print values
#print batch
#print axioms tree_observation
#print axioms parent_observation
#print axioms tree
#print axioms values
#print axioms batch
end NKV_OkTransport
end
