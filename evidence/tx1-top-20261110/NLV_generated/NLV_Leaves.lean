import NLV_Continuation
import NLV_RunLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
def rank (s : NLJ_Tx1.State) : Nat :=
 match s.locals with
 | .guard => 20 | .parse => 19 | .scan => 18 | .markParsed => 17 | .zero => 16
 | .prepare _ => 15 | .accumulator _ _ => 14 | .markPrepare _ _ _ => 13
 | .foldedSlice _ _ _ => 12 | .foldedCopy _ _ _ _ => 11 | .foldedUnwrap _ _ _ _ => 10
 | .batch0 _ _ _ _ => 9 | .markMerkle _ _ _ => 8 | .geometry _ _ _ => 7
 | .pending _ _ _ _ => 6 | .query _ _ _ _ _ => 5 | .finishPending _ _ _ => 4
 | .checkpoint _ _ => 3 | .markCheckpoint _ => 2 | .returned _ => 1
def AllLeaves {A : Type} (P : A → Prop) : Code A → Prop
 | .done a => P a
 | .step _ k => ∀ a, AllLeaves P (k a)
 | .read _ k => ∀ a, AllLeaves P (k a)
theorem leaves_bind {A B : Type} (P : B → Prop) (c : Code A) (k : A → Code B)
 (h : ∀ a, AllLeaves P (k a)) : AllLeaves P (CheckpointBytes5Effect.bind c k) := by
 induction c with
 | done a => exact h a
 | step r f ih => exact fun a => ih a
 | read parts f ih => exact fun a => ih a
/-- An actual returning interpreter value is among the structural leaves. -/
theorem leaves_run {A : Type} (P : A → Prop)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (c : Code A)
 (all : AllLeaves P c) (a : A) (before after : SdkC_Source.Log)
 (returned : SdkC_Source.run h c before=(ok a,after)) : P a := by
 induction c generalizing before with
 | done x => cases returned; exact all
 | step r k ih =>
   cases r with
   | ok x => exact ih x (all x) before returned
   | fail e => cases returned
   | div => cases returned
 | read parts k ih =>
   cases edge : h parts with
   | ok x => exact ih x (all x) _ (by simpa only [SdkC_Source.run,edge] using returned)
   | fail e => simp only [SdkC_Source.run,edge] at returned; cases returned
   | div => simp only [SdkC_Source.run,edge] at returned; cases returned
def FramePost (s : NLJ_Tx1.State) : Post → Prop
 | .inl _ => True
 | .inr after => after.input=s.input
def ProgressPost (s : NLJ_Tx1.State) : Post → Prop
 | .inl _ => True
 | .inr after => rank after<rank s
#print axioms leaves_bind
#print axioms leaves_run
end AspisR1.NLV_Tree
end
