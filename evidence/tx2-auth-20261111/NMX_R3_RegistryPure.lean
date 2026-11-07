import NMX_R3_RegistryEffectLaws
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPure
open Aeneas Aeneas.Std NMX_R3_RegistryEffects

theorem bind {A B : Type} (r : Result A) (k : A → Result B) :
 scalarSpec (r >>= k) = RSL.Spec.bind (scalarSpec r) (fun a => scalarSpec (k a)) := by
 cases r with
 | ok a =>
  change scalarSpec (k a) = RSL.Spec.bind (RSL.Spec.pure a) (fun a => scalarSpec (k a))
  exact (RSL.Spec.bind_pure a (fun a => scalarSpec (k a))).symm
 | fail e =>
  funext env o
  apply propext
  constructor
  · intro h; exact Or.inr (Or.inl ⟨[],rfl,h⟩)
  · intro h
    rcases h with ⟨a,es,tail,hm,_,_⟩ | ⟨es,hm,ho⟩ | ⟨es,hm,_⟩
    · cases hm
    · cases hm; exact ho
    · cases hm
 | div =>
  funext env o
  apply propext
  constructor
  · intro h; exact Or.inr (Or.inr ⟨[],rfl,h⟩)
  · intro h
    rcases h with ⟨a,es,tail,hm,_,_⟩ | ⟨es,hm,_⟩ | ⟨es,hm,ho⟩
    · cases hm
    · cases hm
    · cases hm; exact ho

theorem ite {A : Type} (p : Prop) [Decidable p] (a b : Result A) :
 scalarSpec (if p then a else b) = if p then scalarSpec a else scalarSpec b := by
 by_cases h : p <;> simp only [h,↓reduceIte]

theorem ok {A : Type} (a : A) : scalarSpec (Result.ok a) = RSL.Spec.pure a := rfl
#print axioms ok
#print axioms bind
#print axioms ite
end NMX_R3_RegistryPure
end
