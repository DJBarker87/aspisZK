import NMP_ReachedAlgebra
import NLR_PrepareFinalSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Reached087
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run Log)
/-- Native one-step transcriptions may have arbitrary child replies. Laws are
needed only along the SAME returning prefix, not at unreachable invalid states.
This relation does not assert any physical resource or native-production law. -/
def Agreement {S α : Type} (native model : S → Code (Sum α S)) : Nat → S → Prop
 | 0,_ => True
 | n+1,s => run (native s)=run (model s) ∧
   ∀ log t, run (native s)=(log,.ok (.inr t)) → Agreement native model n t
def fold {S α : Type} (step : S → Code (Sum α S)) : Nat → S → Code α
 | 0,_ => .step (.fail .panic) Code.done
 | n+1,s => PreparedHashCode.bind (step s) (fun p => match p with
   | .inl a => .done a | .inr t => fold step n t)
theorem transport {S α : Type} (native model : S → Code (Sum α S))
 (n : Nat) (s : S) (h : Agreement native model n s) :
 run (fold native n s)=run (fold model n s) := by
 induction n generalizing s with
 | zero => rfl
 | succ n ih =>
  apply NMP_ReachedAlgebra.bind _ _ _ _ h.1
  intro log next reached
  cases next with
  | inl a => rfl
  | inr t => exact ih t (h.2 log t reached)
theorem model_fold (cfg : NLJ_Prepare.Configuration) {H : Type}
 (n : Nat) (s : NLJ_Prepare.State H) :
 fold (NLJ_Prepare.step cfg) n s=NLJ_Prepare.fold cfg n s := by
 induction n generalizing s with
 | zero => rfl
 | succ n ih =>
  simp only [fold,NLJ_Prepare.fold]
  apply congrArg (PreparedHashCode.bind (NLJ_Prepare.step cfg s))
  funext p
  cases p with
  | inl a => rfl
  | inr t => exact ih t
/-- The child's full law remains a parameter of the reached step agreement.
This is a value/log fold support theorem, never a ledger candidate root. -/
theorem source (cfg : NLJ_Prepare.Configuration) {H : Type}
 (i : NLJ_Prepare.Input H)
 (native : NLJ_Prepare.State H → Code (Sum NLJ_Prepare.Out (NLJ_Prepare.State H)))
 (laws : Agreement native (NLJ_Prepare.step cfg) 12 (NLJ_Prepare.initial i)) :
 run (fold native 12 (NLJ_Prepare.initial i))=
 run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) := by
 have h := transport native (NLJ_Prepare.step cfg) 12 (NLJ_Prepare.initial i) laws
 rw [model_fold,NLR_Prepare.source] at h
 exact h
#print axioms transport
#print axioms model_fold
#print axioms source
end AspisR1.NMP_Reached087
end
