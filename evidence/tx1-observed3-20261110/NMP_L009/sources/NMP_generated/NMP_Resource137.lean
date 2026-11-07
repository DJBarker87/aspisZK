import NMP_ResourceFold
import NLJ_ObservedInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Resource137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
open NMP_ResourceFold
/-- The common resource fold specializes to the existing six-phase model. -/
theorem fold_eq {H : Type} (n : Nat) (s : NLJ_Observed.State H) :
 NMP_ResourceFold.fold NLJ_Observed.step n s = NLJ_Observed.fold n s := by
 induction n generalizing s with
 | zero => rfl
 | succ n ih =>
  simp only [NMP_ResourceFold.fold,NLJ_Observed.fold]
  apply congrArg (PreparedHashCode.bind (NLJ_Observed.step s))
  funext p
  cases p with
  | inl a => rfl
  | inr t => exact ih t
/-- Conditional full-outcome fold with correct stopped-resource semantics.
The Chain is still a native-production obligation; this theorem is not a row root. -/
theorem source {H : Type} (i : NLJ_Observed.Input H) (objectId : Nat)
 (before : NLZ_Resources.Heap) (out : Terminal (NLJ_Observed.Out H))
 (log : PreparedHashCode.Log)
 (chain : Chain NLJ_Observed.step objectId 6 (NLJ_Observed.initial i) before out log) :
 run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) = (log,result out) ∧
 (∀ after, finalHeap out = some after → after.objects objectId = before.objects objectId) := by
 have v := NMP_ResourceFold.value chain
 rw [fold_eq,NLJ_Observed.initial_source] at v
 exact ⟨v,NMP_ResourceFold.protected_return chain⟩
#print axioms fold_eq
#print axioms source
#print source
end AspisR1.NMP_Resource137
end
