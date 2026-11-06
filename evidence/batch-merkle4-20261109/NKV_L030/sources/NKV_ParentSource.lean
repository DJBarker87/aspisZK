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

abbrev Caller := Indices → Values → Step
abbrev zeroI : Indices := Array.repeat 16#usize 0#u32
abbrev zeroV : Values := Array.repeat 16#usize (Array.repeat 32#usize 0#u8)

def three (c0 c1 c2 : Caller) : Result Reply := do
 let (r,idx1,val1) ← c0 zeroI zeroV
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue _ =>
   let (r1,idx2,val2) ← c1 idx1 val1
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
   match cf1 with
   | core.ops.control_flow.ControlFlow.Continue _ =>
     let (r2,_,_) ← c2 idx2 val2
     let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
     match cf2 with
     | core.ops.control_flow.ControlFlow.Continue _ => ok (.Ok ())
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         Unit (core.convert.FromSame verifier.Error) residual
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       Unit (core.convert.FromSame verifier.Error) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

theorem three_next (c0 c1 c2 : Caller) :
 three c0 c1 c2=next (c0 zeroI zeroV) (fun i v => next (c1 i v)
   (fun i v => next (c2 i v) (fun _ _ => ok (.Ok ())))) := by
 unfold three next
 cases a : c0 zeroI zeroV with
 | fail e => rfl
 | div => rfl
 | ok out =>
   rcases out with ⟨r,i,v⟩
   cases r with
   | Err e => rfl
   | Ok u =>
     cases u
     simp only [a,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
     cases b : c1 i v with
     | fail e => rfl
     | div => rfl
     | ok out =>
       rcases out with ⟨r,i1,v1⟩
       cases r with
       | Err e => rfl
       | Ok u =>
         cases u
         simp only [b,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
         cases c : c2 i1 v1 with
         | fail e => rfl
         | div => rfl
         | ok out => rcases out with ⟨r,i2,v2⟩;cases r <;> rfl

theorem three_congr (a0 a1 a2 b0 b1 b2 : Caller)
 (first : ∀ i v,reject (a0 i v)=reject (b0 i v))
 (second : ∀ i v,reject (a1 i v)=reject (b1 i v))
 (third : ∀ i v,reject (a2 i v)=reject (b2 i v)) :
 observe (three a0 a1 a2)=observe (three b0 b1 b2) := by
 rw [three_next,three_next]
 apply next_congr _ _ _ _ (first _ _)
 intro i v
 apply next_congr _ _ _ _ (second i v)
 intro i v
 apply next_congr _ _ _ _ (third i v)
 intro i v;rfl

/-- Three SAME-argument calls; complete successful values and first-error
observations. This source support still takes an explicit dictionary. -/
theorem values (base : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (queries : Array U32 22#usize)
 (roots : Array (Array U8 32#usize) 3#usize) (batch : Usize) (bound : batch.val<2) :
 observe (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
   (AspisR1.Port3_BatchStd.install base) D proof queries roots batch hash)=
 observe (NKV_FRef.verifier.candidate.batch_merkle_values
   (AspisR1.Port3_BatchStd.install base) D proof queries roots batch hash) := by
 have h0 : Array.index_usize roots 0#usize=ok (AspisR1.Port3_NativeBatchCalls.rootAt roots 0) :=
   AspisR1.Port3_NativeBatchCalls.root_read roots 0
 have h1 : Array.index_usize roots 1#usize=ok (AspisR1.Port3_NativeBatchCalls.rootAt roots 1) :=
   AspisR1.Port3_NativeBatchCalls.root_read roots 1
 have h2 : Array.index_usize roots 2#usize=ok (AspisR1.Port3_NativeBatchCalls.rootAt roots 2) :=
   AspisR1.Port3_NativeBatchCalls.root_read roots 2
 unfold AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
   NKV_FRef.verifier.candidate.batch_merkle_values
 simp only [h0,h1,h2,bind_tc_ok]
 apply three_congr
 · intro i v;exact NKV_TreeSource.source base D hash proof queries _ batch 0#usize bound i v
 · intro i v;exact NKV_TreeSource.source base D hash proof queries _ batch 1#usize bound i v
 · intro i v;exact NKV_TreeSource.source base D hash proof queries _ batch 2#usize bound i v

set_option pp.proofs false
#print values
#print axioms next_observed
#print axioms next_congr
#print axioms next_question
#print axioms three_next
#print axioms three_congr
#print axioms values
end NKV_ParentSource
end
