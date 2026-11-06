import NKV_TreeSource
import Port3_NativeBatchCalls
set_option autoImplicit false
noncomputable section
namespace NKV_ParentSource
open Aeneas Aeneas.Std Result AspisR1Stage2
open NKV_StepErasure NKV_TreeSource NKV_ReturnBoundary

abbrev Step := Result Return

def observe : Result Reply → Result Unit
 | .ok (.Ok u) => ok u | .ok (.Err _) => fail .panic
 | .fail e => fail e | .div => div

def next (m : Step) (k : Indices → Values → Result Reply) : Result Reply := do
 let (r,i,v) ← m
 match r with | .Ok _ => k i v | .Err e => ok (.Err e)

theorem next_observed (m : Step) (k : Indices → Values → Result Reply) :
 observe (next m k)=(do let (_,i,v) ← reject m; observe (k i v)) := by
 cases m with
 | fail e => rfl
 | div => rfl
 | ok out =>
   rcases out with ⟨r,i,v⟩
   cases r <;> rfl

theorem next_congr (m n : Step) (f g : Indices → Values → Result Reply)
 (head : reject m=reject n) (tail : ∀ i v,observe (f i v)=observe (g i v)) :
 observe (next m f)=observe (next n g) := by
 rw [next_observed,next_observed,head]
 cases reject n with
 | fail e => rfl
 | div => rfl
 | ok out => rcases out with ⟨u,i,v⟩;exact tail i v

theorem next_question (m : Step) (k : Indices → Values → Result Reply) :
 (do let (r,i,v) ← m
     let cf ← core.result.Result.Insts.CoreOpsTry.branch r
     match cf with
     | core.ops.control_flow.ControlFlow.Continue _ => k i v
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         Unit (core.convert.FromSame verifier.Error) residual)=next m k := by
 cases m with
 | fail e => rfl
 | div => rfl
 | ok out => rcases out with ⟨r,i,v⟩;cases r <;> rfl

/-- Three SAME-argument tree calls with arrays threaded only through Ok.
The two source programs may differ in returned-error representation, but their
complete successful values and first rejection observations agree. -/
theorem values (base : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (queries : Array U32 22#usize)
 (roots : Array (Array U8 32#usize) 3#usize) (batch : Usize) (bound : batch.val<2) :
 observe (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
   (AspisR1.Port3_BatchStd.install base) D proof queries roots batch hash)=
 observe (NKV_FRef.verifier.candidate.batch_merkle_values
   (AspisR1.Port3_BatchStd.install base) D proof queries roots batch hash) := by
 have h0 := AspisR1.Port3_NativeBatchCalls.root_read roots 0
 have h1 := AspisR1.Port3_NativeBatchCalls.root_read roots 1
 have h2 := AspisR1.Port3_NativeBatchCalls.root_read roots 2
 unfold AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
   NKV_FRef.verifier.candidate.batch_merkle_values
 simp only [h0,h1,h2,bind_tc_ok]
 simp only [next_question]
 change observe (next _ (fun i v => next _ (fun i v => next _ (fun _ _ => ok (.Ok ())))))=
   observe (next _ (fun i v => next _ (fun i v => next _ (fun _ _ => ok (.Ok ())))))
 apply next_congr
 · exact NKV_TreeSource.source base D hash proof queries _ batch 0#usize bound _ _
 · intro i v
   apply next_congr
   · exact NKV_TreeSource.source base D hash proof queries _ batch 1#usize bound i v
   · intro i v
     apply next_congr
     · exact NKV_TreeSource.source base D hash proof queries _ batch 2#usize bound i v
     · intro i v;rfl

set_option pp.proofs false
#print values
#print axioms next_observed
#print axioms next_congr
#print axioms next_question
#print axioms values
end NKV_ParentSource
end
