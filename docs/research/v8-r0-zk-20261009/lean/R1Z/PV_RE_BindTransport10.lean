import R1Z.PV_RE_ClientEntry
set_option autoImplicit false
namespace R1Z.PV_RE_BindTransport10
open Aeneas Aeneas.Std Result

/-- Compose a complete source prefix while keeping both remaining suffixes. -/
theorem compose {A B C : Type} (whole : Result C) (middle : Result B)
    (first : Result A) (hm : ∃ next, whole = middle >>= next)
    (hf : ∃ next, middle = first >>= next) :
    ∃ next, whole = first >>= next := by
  obtain ⟨k,hk⟩ := hm
  obtain ⟨j,hj⟩ := hf
  rw [hj,PV_RE_ClientEntry.bind_assoc] at hk
  exact ⟨_,hk⟩

/-- A failed or divergent prefix cannot be resumed by a Result suffix. -/
theorem failure {A B : Type} (prefix : Result A) (next : A → Result B)
    (e : Error) (h : prefix = .fail e) : prefix >>= next = .fail e := by
  rw [h]; rfl

theorem divergence {A B : Type} (prefix : Result A) (next : A → Result B)
    (h : prefix = .div) : prefix >>= next = .div := by
  rw [h]; rfl
#print axioms compose
#print axioms failure
#print axioms divergence
end R1Z.PV_RE_BindTransport10
