import NMP_ResourceFold
import NLR_PrepareFinalSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Resource087
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
open NMP_ResourceFold
theorem fold_eq (cfg : NLJ_Prepare.Configuration) {H : Type}
 (n : Nat) (s : NLJ_Prepare.State H) :
 NMP_ResourceFold.fold (NLJ_Prepare.step cfg) n s = NLJ_Prepare.fold cfg n s := by
 induction n generalizing s with
 | zero => rfl
 | succ n ih =>
  simp only [NMP_ResourceFold.fold,NLJ_Prepare.fold]
  apply congrArg (PreparedHashCode.bind (NLJ_Prepare.step cfg s))
  funext p
  cases p with
  | inl a => rfl
  | inr t => exact ih t
/-- The native producer must discharge the source cut and physical frame at
each of the twelve phases, including SAME 137/179 and g writeback. -/
theorem source (cfg : NLJ_Prepare.Configuration) {H : Type}
 (i : NLJ_Prepare.Input H) (objectId : Nat) (before : NLZ_Resources.Heap)
 (out : Terminal NLJ_Prepare.Out) (log : PreparedHashCode.Log)
 (chain : Chain (NLJ_Prepare.step cfg) objectId 12 (NLJ_Prepare.initial i) before out log) :
 run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) = (log,result out) ∧
 (∀ after, finalHeap out = some after → after.objects objectId = before.objects objectId) := by
 have v := NMP_ResourceFold.value chain
 rw [fold_eq,NLR_Prepare.source] at v
 exact ⟨v,NMP_ResourceFold.protected_return chain⟩
#print axioms fold_eq
#print axioms source
#print source
end AspisR1.NMP_Resource087
end
