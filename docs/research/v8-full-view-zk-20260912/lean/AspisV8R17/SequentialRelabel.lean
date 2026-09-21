import AspisV8R17.RejectionCursor
import Mathlib.Data.Fintype.Vector

/-! Per-limb relabeling advances only at accepted words. It is a bijection
on full tapes, including tapes that exhaust a bounded scan. -/
set_option autoImplicit false
namespace AspisV8R17.SequentialRelabel
open AspisV8R17.RejectionCursor
variable {D : Type*}

def relabel (accept : D → Bool) (es : List (D ≃ D)) : List D → List D
  | [] => []
  | x::xs => match es with
    | [] => x::xs
    | e::tail => e x :: relabel accept (if accept x then tail else es) xs

theorem relabel_length (accept : D → Bool) (es : List (D ≃ D)) (xs : List D) :
    (relabel accept es xs).length = xs.length := by
  induction xs generalizing es with
  | nil => rfl
  | cons x xs ih => cases es <;> simp [relabel, ih]

theorem relabel_inverse (accept : D → Bool) (es : List (D ≃ D))
    (hp : ∀ e ∈ es, ∀ x, accept (e x) = accept x) (xs : List D) :
    relabel accept (es.map Equiv.symm) (relabel accept es xs) = xs := by
  induction xs generalizing es with
  | nil => rfl
  | cons x xs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      have he := hp e (by simp) x
      have ht : ∀ f ∈ es, ∀ y, accept (f y) = accept y := by
        intro f hf
        exact hp f (by simp [hf])
      cases hx : accept x with
      | false => simpa [relabel, he, hx] using ih (e::es) hp
      | true => simpa [relabel, he, hx] using ih es ht

theorem scan_relabel (accept : D → Bool) (e : D ≃ D) (es : List (D ≃ D))
    (hp : ∀ x, accept (e x) = accept x) (fuel : ℕ) (xs : List D) :
    scan accept fuel (relabel accept (e::es) xs) =
      (scan accept fuel xs).map (fun p => (e p.1, relabel accept es p.2)) := by
  induction fuel generalizing xs with
  | zero => simp [scan]
  | succ fuel ih =>
    cases xs with
    | nil => simp [relabel, scan]
    | cons x xs => cases hx : accept x <;> simp [relabel, scan, hp, hx, ih]

theorem scanMany_relabel (accept : D → Bool) (es : List (D ≃ D))
    (hp : ∀ e ∈ es, ∀ x, accept (e x) = accept x) (fuel : ℕ) (xs : List D) :
    scanMany accept fuel es.length (relabel accept es xs) =
      (scanMany accept fuel es.length xs).map
        (fun p => (List.zipWith (fun (e : D ≃ D) x => e x) es p.1, p.2)) := by
  induction es generalizing xs with
  | nil => cases xs <;> simp [relabel, scanMany]
  | cons e es ih =>
    have he : ∀ x, accept (e x) = accept x := hp e (by simp)
    have ht : ∀ f ∈ es, ∀ x, accept (f x) = accept x := by
      intro f hf
      exact hp f (by simp [hf])
    simp only [List.length_cons, scanMany, scan_relabel accept e es he]
    cases hs : scan accept fuel xs with
    | none => simp
    | some pair =>
      rcases pair with ⟨x,rest⟩
      simp only [Option.map_some]
      simp [ih ht]
      cases scanMany accept fuel es.length rest <;> rfl

theorem inverse_preserves (accept : D → Bool) (es : List (D ≃ D))
    (hp : ∀ e ∈ es, ∀ x, accept (e x) = accept x) :
    ∀ e ∈ es.map Equiv.symm, ∀ x, accept (e x) = accept x := by
  intro e he x
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  simpa using (hp f hf (f.symm x)).symm

def tapeEquiv (accept : D → Bool) (es : List (D ≃ D))
    (hp : ∀ e ∈ es, ∀ x, accept (e x) = accept x) (n : ℕ) :
    List.Vector D n ≃ List.Vector D n where
  toFun xs := ⟨relabel accept es xs.val, (relabel_length accept es xs.val).trans xs.property⟩
  invFun xs := ⟨relabel accept (es.map Equiv.symm) xs.val,
    (relabel_length accept _ xs.val).trans xs.property⟩
  left_inv xs := by
    apply Subtype.ext
    exact relabel_inverse accept es hp xs.val
  right_inv xs := by
    apply Subtype.ext
    simpa [List.map_map, Function.comp_def] using
      relabel_inverse accept (es.map Equiv.symm) (inverse_preserves accept es hp) xs.val

local instance [Nonempty D] (n : ℕ) : Nonempty (List.Vector D n) :=
  Nonempty.map (Equiv.vectorEquivFin D n).symm inferInstance

theorem joint_uniform_symmetry [Fintype D] [Nonempty D]
    (accept : D → Bool) (es : List (D ≃ D))
    (hp : ∀ e ∈ es, ∀ x, accept (e x) = accept x) (fuel n : ℕ) :
    AspisV8Privacy.SameUniformLaw
      (fun xs : List.Vector D n => (scanMany accept fuel es.length xs.val).map
        (fun p => (List.zipWith (fun (e : D ≃ D) x => e x) es p.1, p.2)))
      (fun xs : List.Vector D n => scanMany accept fuel es.length xs.val) := by
  apply AspisV8Privacy.sameUniformLaw_of_coinEquiv _ _ (tapeEquiv accept es hp n)
  intro xs
  exact scanMany_relabel accept es hp fuel xs.val

#print axioms inverse_preserves
#print axioms joint_uniform_symmetry
#print axioms relabel_length
#print axioms relabel_inverse
#print axioms scan_relabel
#print axioms scanMany_relabel
end AspisV8R17.SequentialRelabel
