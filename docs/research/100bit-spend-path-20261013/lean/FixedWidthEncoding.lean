import Mathlib.Data.List.OfFn

/-! Injectivity of list encodings assembled by flattening equal-width blocks. -/
set_option autoImplicit false

namespace AspisR1.FixedWidthEncoding

theorem flatMap_injective {A B : Type} (f : A → List B) (n : Nat)
    (hn : 0 < n) (hlen : ∀ a, (f a).length = n)
    (hinj : Function.Injective f) :
    Function.Injective (fun xs : List A => xs.flatMap f) := by
  intro xs ys hxy
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          simp only [List.flatMap_nil, List.flatMap_cons] at hxy
          have hnil : f y ++ ys.flatMap f = [] := hxy.symm
          rw [List.append_eq_nil_iff] at hnil
          obtain ⟨hfy, _⟩ := hnil
          have hy := hlen y
          have : 0 = n := by simpa [hfy] using hy
          omega
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [List.flatMap_cons, List.flatMap_nil] at hxy
          have hnil : f x ++ xs.flatMap f = [] := hxy
          rw [List.append_eq_nil_iff] at hnil
          obtain ⟨hfx, _⟩ := hnil
          have hx := hlen x
          have : 0 = n := by simpa [hfx] using hx
          omega
      | cons y ys =>
          have hheadLen : (f x).length = (f y).length := by
            rw [hlen x, hlen y]
          have hparts := List.append_inj hxy hheadLen
          rcases hparts with ⟨hhead, htail⟩
          have hxy' : x = y := hinj hhead
          subst y
          congr 1
          exact ih htail

theorem ofFn_flatMap_injective {A B : Type} (f : A → List B) (n m : Nat)
    (hn : 0 < n) (hlen : ∀ a, (f a).length = n)
    (hinj : Function.Injective f) :
    Function.Injective
      (fun xs : Fin m → A => (List.ofFn xs).flatMap f) := by
  intro xs ys hxy
  apply List.ofFn_injective
  exact flatMap_injective f n hn hlen hinj hxy

#print axioms flatMap_injective
#print axioms ofFn_flatMap_injective

end AspisR1.FixedWidthEncoding
