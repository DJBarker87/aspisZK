import NKV_Progress
set_option autoImplicit false
noncomputable section
namespace NKV_BoundedLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary

/-- At most n-pos native iterations plus the terminal tail. Child fail/div
terminates at that call; no successful-child hypothesis is needed. -/
theorem finite (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (bound : n.val≤12)
 (i : Indices) (v : Values) (d pos : Usize) :
 ∃ out,Walk (fun (i,v,d,p) => NKV_FRef.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys i v d p) (i,v,d,pos) out := by
 let body := fun (i,v,d,p) => NKV_FRef.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys i v d p
 have total : ∀ fuel, ∀ (i : Indices) (v : Values) (d pos : Usize),
     n.val-pos.val=fuel → ∃ out,Walk body (i,v,d,pos) out := by
   intro fuel
   induction fuel using Nat.strong_induction_on with
   | h fuel ih =>
     intro i v d pos eq
     cases step : body (i,v,d,pos) with
     | fail e => exact ⟨fail e,.failed _ e step⟩
     | div => exact ⟨div,.diverged _ step⟩
     | ok flow =>
       cases flow with
       | done out => exact ⟨ok out,.done _ out step⟩
       | cont state =>
         rcases state with ⟨ai,av,ad,apos⟩
         have cursor := NKV_Progress.continues ops D proof root tree hash lo n slot keys
           i ai v av d pos ad apos step
         have active : pos.val<n.val := cursor.2
         have advance : apos.val=pos.val+1 := by
           rw [cursor.1]
           exact AspisR1.Port3_Wrapping.increment pos (by omega)
         have less : n.val-apos.val<fuel := by omega
         obtain ⟨out,tail⟩:=ih (n.val-apos.val) less ai av ad apos rfl
         exact ⟨out,.next _ _ out step tail⟩
 exact total (n.val-pos.val) i v d pos rfl

def Valid : Result Out → Prop
 | .ok out => WellClassified out | .fail _ => True | .div => True

theorem classified (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (s : State) (out : Result Out)
 (walk : Walk (fun (i,v,d,p) => NKV_FRef.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys i v d p) s out) : Valid out := by
 induction walk with
 | done s out step =>
   rcases s with ⟨i,v,d,p⟩
   exact NKV_Progress.done_classified ops D proof root tree hash lo n slot keys i v d p out step
 | failed s e step => trivial
 | diverged s step => trivial
 | next s t out step tail ih => exact ih

/-- Both complete loop values, SAME initial buffers, arbitrary child Results.
This is source support only: it contains an Ops parameter, outside aq(2). -/
theorem source (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (bound : n.val≤12)
 (i : Indices) (v : Values) (d pos : Usize) :
 ∃ out, Valid out ∧
 NKV_FRef.verifier.candidate.batch_tree_loop ops D proof root tree i v hash lo n slot keys d pos=out ∧
 AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
   ops D proof root tree i v hash lo n slot keys d pos=mapResult eraseOut out := by
 obtain ⟨out,walk⟩:=finite ops D proof root tree hash lo n slot keys bound i v d pos
 exact ⟨out,classified ops D proof root tree hash lo n slot keys _ _ walk,
   execute _ _ _ walk,NKV_LoopTransport.source ops D proof root tree hash lo n slot keys _ _ walk⟩

set_option pp.proofs false
#print source
#print axioms finite
#print axioms classified
#print axioms source
end NKV_BoundedLoop
end
