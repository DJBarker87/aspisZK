import R1Z.PV_RE_ClientEntry
set_option autoImplicit false
namespace R1Z.PV_RE_BindTransportB10
open Aeneas Aeneas.Std Result

/-- Compose a complete source prefix while keeping both remaining suffixes. -/
theorem compose {A B C : Type} (whole : Result C) (middle : Result B)
    (first : Result A) (hm : ∃ next, whole = middle >>= next)
    (hf : ∃ next, middle = first >>= next) :
    ∃ next, whole = first >>= next := by
  obtain ⟨k,hk⟩ := hm
  obtain ⟨j,hj⟩ := hf
  have assoc {X Y Z : Type} (x : Result X) (f : X → Result Y) (g : Y → Result Z) :
      ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
    cases x <;> rfl
  rw [hj,assoc] at hk
  exact ⟨_,hk⟩

/-- A failed or divergent prefix cannot be resumed by a Result suffix. -/
theorem failure {A B : Type} (call : Result A) (next : A → Result B)
    (e : Error) (h : call = .fail e) : call >>= next = .fail e := by
  rw [h]; rfl

theorem divergence {A B : Type} (call : Result A) (next : A → Result B)
    (h : call = .div) : call >>= next = .div := by
  rw [h]; rfl
#print axioms compose
#print axioms failure
#print axioms divergence
end R1Z.PV_RE_BindTransportB10
