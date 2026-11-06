import NJM_CircleCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_CircleNative
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
open NIX_DispatchCut

def row (r : U8) : FinishModel.CircleRow := if r==25#u8 then .First else .Second

/-- Substitute the CLOSED circle reply on the SAME logged block and branch.
The native cut's other oracle and local-frame inputs remain unchanged. -/
def install {Pointer : Type} (s : Pre Pointer) : Pre Pointer :=
 {s with point:=match s.reply with
  | .Ok b=>NJM_CircleJoin.point b (row s.row)
  | .Err _=>s.point}

/-- Complete continuation equality at a valid native branch, including the
child's error post-state. The hypothesis is exactly the reviewed K049/K050 cut.
No circle output equation, successful child, or operation dictionary is assumed. -/
theorem returned {Pointer H : Type} (s : Pre Pointer) (p : Post Pointer)
 (t : r1_wire.SemanticTranscript H)
 (cut : NIX_DispatchCut.cut (install s) p) (valid : NIX_DispatchCut.valid s.row=true) :
 p.transcriptState=s.newState ∧ p.transcriptNext=s.newNext ∧ p.frame=s.frame ∧
 run (NJM_CircleJoin.after (row s.row) (s.reply,t))=([],ok (p.result,t)) := by
 have post := cut.2.2.2.2.1
 have result := cut.2.2.2.2.2
 have frame := cut.2.2.2.1
 change (if NIX_DispatchCut.valid s.row then _ else _) at post
 rw [if_pos valid] at post
 refine ⟨post.2.2.2.2.2.2.1,post.2.2.2.2.2.2.2.1,frame,?_⟩
 have res : p.result=(match s.reply with
  | .Ok b=>.Ok (NJM_CircleJoin.point b (row s.row))
  | .Err e=>.Err e) := by
  simpa only [expected,install,valid,if_true] using result
 rw [res]
 cases s.reply <;> rfl

/-- Invalid-row cut has no child suffix and preserves the full transcript. -/
theorem invalid {Pointer : Type} (s : Pre Pointer) (p : Post Pointer)
 (cut : NIX_DispatchCut.cut (install s) p) (invalid : NIX_DispatchCut.valid s.row=false) :
 p.result=.Err .InvalidRow ∧ p.transcriptState=s.state ∧ p.transcriptNext=s.next ∧
 p.count=s.count ∧ p.frame=s.frame := by
 have post := cut.2.2.2.2.1
 change (if NIX_DispatchCut.valid s.row then _ else _) at post
 rw [if_neg (by simp only [invalid,Bool.false_eq_true,not_false_eq_true])] at post
 exact ⟨NIX_DispatchCut.invalid_result (install s) p cut invalid,post.1,post.2.1,post.2.2.1,cut.2.2.2.1⟩

#print axioms returned
#print axioms invalid
end AspisR1.NJM_CircleNative
end
