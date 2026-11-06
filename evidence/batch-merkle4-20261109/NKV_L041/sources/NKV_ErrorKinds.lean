import NKV_BoundedLoop
import Port3_BatchStd
set_option autoImplicit false
noncomputable section
namespace NKV_ErrorKinds
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1
open NKV_StepErasure NKV_LoopTransport

def Allowed : Reply → Prop | .Ok _ => True | .Err e => e=.Parse ∨ e=.Merkle

theorem step_error (base : Port3_NativeBatchBody.Ops) {X : Type}
 (D : aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize)
 (keys : Array U64 16#usize) (idx ai : Indices) (val av : Values) (d pos : Usize)
 (e : verifier.Error) (lost : Bool)
 (h : NKV_FRef.verifier.candidate.batch_tree_loop.body (Port3_BatchStd.install base)
   D proof root tree hash lo n slot keys idx val d pos=ok (.done (ai,av,.Err e,lost))) :
 e=.Parse ∨ e=.Merkle := by
 unfold NKV_FRef.verifier.candidate.batch_tree_loop.body at h
 simp only [Port3_BatchStd.install,Port3_BatchStd.okOr] at h
 repeat' first
 | (solve | cases h)
 | uncase_result
 | head_reduce h
 | split at h
 all_goals
   cases Result.ok.inj h
   first | exact Or.inl rfl | exact Or.inr rfl

def LoopAllowed : Result Out → Prop
 | .ok out => Allowed out.2.2.1 | .fail _ => True | .div => True

theorem walk (base : Port3_NativeBatchBody.Ops) {X : Type}
 (D : aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize)
 (keys : Array U64 16#usize) (s : NKV_StepErasure.State) (out : Result Out)
 (native : Walk (fun (i,v,d,p) => NKV_FRef.verifier.candidate.batch_tree_loop.body
   (Port3_BatchStd.install base) D proof root tree hash lo n slot keys i v d p) s out) :
 LoopAllowed out := by
 induction native with
 | failed s e step => trivial
 | diverged s step => trivial
 | next s t out step tail ih => exact ih
 | done s out step =>
   rcases s with ⟨i,v,d,p⟩
   rcases out with ⟨ai,av,r,lost⟩
   cases r with
   | Ok u => trivial
   | Err e => exact step_error base D hash proof root tree lo n slot keys i ai v av d p e lost step

theorem loop (base : Port3_NativeBatchBody.Ops) {X : Type}
 (D : aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize)
 (keys : Array U64 16#usize) (bound : n.val≤12)
 (idx : Indices) (val : Values) (d pos : Usize) :
 LoopAllowed (NKV_FRef.verifier.candidate.batch_tree_loop (Port3_BatchStd.install base)
   D proof root tree idx val hash lo n slot keys d pos) := by
 obtain ⟨out,native⟩:=NKV_BoundedLoop.finite (Port3_BatchStd.install base) D proof root tree hash
   lo n slot keys bound idx val d pos
 rw [show NKV_FRef.verifier.candidate.batch_tree_loop (Port3_BatchStd.install base)
   D proof root tree idx val hash lo n slot keys d pos=out from execute _ _ _ native]
 exact walk base D hash proof root tree lo n slot keys _ _ native

set_option pp.proofs false
#print loop
#print axioms step_error
#print axioms walk
#print axioms loop
end NKV_ErrorKinds
end
