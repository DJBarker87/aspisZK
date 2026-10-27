import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RE_NoCatchCore
open Aeneas.Std
/-- An error entering this continuation cannot be caught or changed. -/
def NoCatch {α β : Type} (k : Result α → Result β) : Prop :=
  (∀ e, k (.fail e) = .fail e) ∧ k .div = .div

theorem bind_noCatch {α β : Type} (k : α → Result β) :
    NoCatch (fun r => r >>= k) := by
  constructor
  · intro e; rfl
  · rfl

theorem compose {α β γ : Type} {f : Result α → Result β}
    {g : Result β → Result γ} (hf : NoCatch f) (hg : NoCatch g) :
    NoCatch (g ∘ f) := by
  constructor
  · intro e; change g (f (.fail e)) = .fail e
    rw [hf.1 e, hg.1 e]
  · change g (f .div) = .div
    rw [hf.2, hg.2]

/-- Poison exclusion needs a source invocation-to-failure witness, separately
from dictionary congruence. No invocation semantics is defined here. -/
theorem exclusion_by_poisoning {I O : Type} (admitted : I → Prop)
    (run poisoned : I → Result O) (invoked : I → Prop)
    (congruent : ∀ i, admitted i → poisoned i = run i)
    (noCatch : ∀ i, admitted i → invoked i →
      ∃ e, poisoned i = .fail e) :
    ∀ i, admitted i → (∃ v, run i = .ok v) → ¬ invoked i := by
  intro i hi hs hr
  obtain ⟨e, he⟩ := noCatch i hi hr
  obtain ⟨v, hv⟩ := hs
  rw [congruent i hi, hv] at he
  cases he

/-- On a failed run congruence and absorption alone cannot exclude invocation. -/
theorem failed_run_compatible (e : Error) :
    ((.fail e : Result Unit) = .fail e) ∧
    (∃ err, (.fail e : Result Unit) = .fail err) :=
  ⟨rfl, e, rfl⟩

#print axioms NoCatch
#print axioms bind_noCatch
#print axioms compose
#print axioms exclusion_by_poisoning
#print axioms failed_run_compatible
end R1Z.PV_RE_NoCatchCore
