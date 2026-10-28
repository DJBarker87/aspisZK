import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_Slice194
open Aeneas Aeneas.Std Result ControlFlow
/-- Direct1.94.1 generic SlicePartialEq loop at the existing checked-index and
    scalar primitive boundary. Nat indices below the slice length are justified
    separately by increment_safe; no callback is assumed successful. -/
def body {A B : Type} (xs : List A) (ys : List B) (p : core.cmp.PartialEq A B)
    (i : Nat) : Result (ControlFlow Nat Bool) := do
  if i < xs.length then
    match xs[i]?, ys[i]? with
    | some a, some b =>
      let different ← p.ne a b
      if different then ok (done false) else ok (cont (i+1))
    | _, _ => fail .arrayOutOfBounds
  else ok (done true)

def source {A B : Type} (xs : List A) (ys : List B) (p : core.cmp.PartialEq A B) : Result Bool :=
  if xs.length = ys.length then loop (body xs ys p) 0 else ok false

def compare {A B : Type} (p : core.cmp.PartialEq A B) (xy : A × B) : Result Bool := do
  let different ← p.ne xy.1 xy.2
  ok (!different)

theorem increment_safe (i length limit : Nat) (hi : i < length) (hl : length ≤ limit) :
    i+1 ≤ limit := by omega

theorem loop_suffix {A B : Type} (xs : List A) (ys : List B) (p : core.cmp.PartialEq A B)
    (lengths : xs.length = ys.length) (i : Nat) (hi : i ≤ xs.length) :
    loop (body xs ys p) i = List.allM (compare p) ((xs.drop i).zip (ys.drop i)) := by
  suffices ∀ n i, xs.length-i=n → i ≤ xs.length →
    loop (body xs ys p) i = List.allM (compare p) ((xs.drop i).zip (ys.drop i)) from
    this (xs.length-i) i rfl hi
  intro n
  induction n with
  | zero =>
    intro i hn hi
    have he : i=xs.length := by omega
    subst i
    rw [loop.eq_def]
    simp [body, lengths] <;> rfl
  | succ n ih =>
    intro i hn hi
    have hx : i < xs.length := by omega
    have hy : i < ys.length := by omega
    have hn1 : xs.length-(i+1)=n := by omega
    have next := ih (i+1) hn1 (by omega)
    rw [loop.eq_def]
    rw [List.drop_eq_getElem_cons hx,List.drop_eq_getElem_cons hy]
    simp only [body, hx, if_true, List.getElem?_eq_getElem hx,
      List.getElem?_eq_getElem hy, List.zip_cons_cons, List.allM]
    cases hne : p.ne xs[i] ys[i] with
    | ok different => cases different <;> simp [compare,hne,next] <;> rfl
    | fail e => simp [compare,hne]
    | div => simp [compare,hne]

theorem source_model {A B : Type} (xs : List A) (ys : List B) (p : core.cmp.PartialEq A B) :
    source xs ys p =
    (if xs.length = ys.length then List.allM (compare p) (xs.zip ys) else ok false) := by
  unfold source
  split
  next h => simpa using loop_suffix xs ys p h 0 (by omega)
  next h => rfl

#print axioms increment_safe
#print axioms loop_suffix
#print axioms source_model
end R1Z.PV_RDCD_Slice194
