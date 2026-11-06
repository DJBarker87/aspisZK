import NKV_BoundedLoop
import Port3_BatchStd
set_option autoImplicit false
noncomputable section
namespace NKV_TreeSource
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary

abbrev Return := Reply × Indices × Values

def finish : CohortOut → Result Return
 | (i,v,none) => fail .panic
 | (i,v,some r) => ok (r,i,v)

theorem boundary (out : Result Out) (valid : NKV_BoundedLoop.Valid out) :
 reject (mapResult eraseOut out >>= finish)=reject (out >>= returned) := by
 cases out with
 | fail e => rfl
 | div => rfl
 | ok x => exact observed x valid

theorem bind_observed {A : Type} (m : Result A) (f g : A → Result Return)
 (same : ∀ x,reject (f x)=reject (g x)) :
 reject (m >>= f)=reject (m >>= g) := by
 cases m with
 | fail e => rfl
 | div => rfl
 | ok x => exact same x

def treeWith (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (idx : Indices) (val : Values) : Result Return := do
 let a ← ops.op4 queries lo n tree
 let keys ← ops.op5 a n
 let out ← AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
   ops D proof root tree idx val hash lo n slot keys 0#usize 0#usize
 finish out

def refWith (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (idx : Indices) (val : Values) : Result Return := do
 let a ← ops.op4 queries lo n tree
 let keys ← ops.op5 a n
 let out ← NKV_FRef.verifier.candidate.batch_tree_loop
   ops D proof root tree idx val hash lo n slot keys 0#usize 0#usize
 returned out

theorem prefix_source (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (bound : n.val≤12) (idx : Indices) (val : Values) :
 reject (treeWith ops D hash proof queries root tree lo n slot idx val)=
 reject (refWith ops D hash proof queries root tree lo n slot idx val) := by
 unfold treeWith refWith
 apply bind_observed
 intro raw
 apply bind_observed
 intro keys
 obtain ⟨out,valid,native,ref⟩ := NKV_BoundedLoop.source ops D proof root tree hash
   lo n slot keys bound idx val 0#usize 0#usize
 rw [native,ref]
 exact boundary out valid

/-- Full source-level return observation, no accepted-run premise and no
finite-Walk premise. Ops remains SUPPORT ONLY outside aq(2). -/
theorem source (base : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (batch tree : Usize) (bound : batch.val<2) (idx : Indices) (val : Values) :
 reject (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree
   (AspisR1.Port3_BatchStd.install base) D proof queries root batch tree idx val hash)=
 reject (NKV_FRef.verifier.candidate.batch_tree
   (AspisR1.Port3_BatchStd.install base) D proof queries root batch tree idx val hash) := by
 have batches : batch=0#usize ∨ batch=1#usize := by
   by_cases zero : batch.val=0
   · exact Or.inl (UScalar.eq_of_val_eq zero)
   · exact Or.inr (UScalar.eq_of_val_eq (by change batch.val=1;omega))
 rcases batches with rfl|rfl
 all_goals
   unfold AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree
     NKV_FRef.verifier.candidate.batch_tree
   simp only [AspisR1.Port3_BatchStd.install,lift,bind_tc_ok,↓reduceIte]
   try dsimp only
 · exact prefix_source (AspisR1.Port3_BatchStd.install base) D hash proof queries root tree
       0#usize (Usize.wrapping_sub 10#usize 0#usize)
       (Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) tree)
       (by rw [Usize.wrapping_sub_val_eq]; scalar_tac) idx val
 · exact prefix_source (AspisR1.Port3_BatchStd.install base) D hash proof queries root tree
       10#usize (Usize.wrapping_sub 22#usize 10#usize)
       (Usize.wrapping_add (Usize.wrapping_mul 3#usize 1#usize) tree)
       (by rw [Usize.wrapping_sub_val_eq]; scalar_tac) idx val

set_option pp.proofs false
#print source
#print axioms boundary
#print axioms bind_observed
#print axioms prefix_source
#print axioms source
end NKV_TreeSource
end
