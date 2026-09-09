import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

/-! Short-circuit canonical collection, independent of concrete field size or
field-count numerals. The output relation is derived from execution, not
supplied to the parser bridge. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 10000
namespace AspisV8.CanonicalCollect
variable {A B : Type*}

def collect (decode : A → Option B) : List A → Option (List B)
  | [] => some []
  | x::xs => do
    let y ← decode x
    let ys ← collect decode xs
    pure (y::ys)

theorem success_forall (decode : A → Option B) (xs : List A) (ys : List B)
    (success : collect decode xs=some ys) :
    List.Forall₂ (fun x y=>decode x=some y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    have same : []=ys := by simpa only [collect,Option.some.injEq] using success
    subst ys
    exact List.Forall₂.nil
  | cons x xs ih =>
    cases hx : decode x with
    | none => simp [collect,hx] at success
    | some y =>
      cases ht : collect decode xs with
      | none => simp [collect,hx,ht] at success
      | some rest =>
        have same : y::rest=ys := by simpa [collect,hx,ht] using success
        subst ys
        exact List.Forall₂.cons hx (ih rest ht)

/-- Generic ofFn readback: no concrete field-count vector is reduced. -/
theorem success_ofFn (decode : A → Option B) {n : Nat} (fields : Fin n → A)
    (values : List B) (default : B)
    (success : collect decode (List.ofFn fields)=some values) :
    values.length=n ∧ ∀ i : Fin n, decode (fields i)=some (values.getD i.val default) := by
  have paired := success_forall decode (List.ofFn fields) values success
  have length : values.length=n := by
    simpa only [List.length_ofFn] using paired.length_eq.symm
  refine ⟨length,?_⟩
  intro i
  have leftBound : i.val<(List.ofFn fields).length := by
    simpa only [List.length_ofFn] using i.isLt
  have rightBound : i.val<values.length := by rw [length]; exact i.isLt
  have entry := paired.get leftBound rightBound
  rw [List.getD_eq_getElem _ _ rightBound]
  simpa only [List.get_eq_getElem,List.getElem_ofFn] using entry

#print axioms success_forall
#print axioms success_ofFn
end AspisV8.CanonicalCollect
