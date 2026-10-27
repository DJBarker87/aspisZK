import Aeneas
/-! Successful checked scalar operations equal their release wrapping forms.
These are kernel theorems about the backend operations, not a compiler law. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWrapping47
open Aeneas Aeneas.Std Result

def Refines {A B : Type} (f : A → B) (checked : Result A) (release : Result B) : Prop :=
  ∀ x, checked=ok x → release=ok (f x)

theorem bind {A B C D : Type} (f : A → B) (g : C → D)
    (c : Result A) (r : Result B) (k : A → Result C) (l : B → Result D)
    (first : Refines f c r) (next : ∀ a, Refines g (k a) (l (f a))) :
    Refines g (c >>= k) (r >>= l) := by
  intro x hx
  cases hc : c with
  | fail e => simp only [hc,bind_tc_fail] at hx; cases hx
  | div => simp only [hc,bind_tc_div] at hx; cases hx
  | ok a =>
    have hr := first a hc
    simp only [hc,bind_tc_ok] at hx
    rw [hr]
    exact next a x hx

theorem refl {A : Type} (r : Result A) : Refines id r r := by intro x h;exact h

theorem pure {A B : Type} (f : A → B) (x : A) : Refines f (ok x) (ok (f x)) := by
  intro y h
  cases h
  rfl

theorem wrap_add {ty : UScalarTy} (x y z : UScalar ty) (h : UScalar.add x y=ok z) :
    UScalar.wrapping_add x y=z := by
  have he := UScalar.add_equiv x y
  have hp : x + y = ok z := h
  rw [hp] at he
  change UScalar.mk (x.bv+y.bv)=z
  rw [← he.2.2]

theorem wrap_sub {ty : UScalarTy} (x y z : UScalar ty) (h : UScalar.sub x y=ok z) :
    UScalar.wrapping_sub x y=z := by
  have he := UScalar.sub_equiv x y
  have hp : x - y = ok z := h
  rw [hp] at he
  change UScalar.mk (x.bv-y.bv)=z
  rw [← he.2.2]

theorem wrap_mul {ty : UScalarTy} (x y z : UScalar ty) (h : UScalar.mul x y=ok z) :
    UScalar.wrapping_mul x y=z := by
  have he := UScalar.mul_equiv x y
  rw [h] at he
  change UScalar.mk (x.bv*y.bv)=z
  rw [← he.2.2]

theorem add {ty : UScalarTy} (x y : UScalar ty) :
    Refines id (UScalar.add x y) (ok (UScalar.wrapping_add x y)) := by
  intro z hz
  exact congrArg ok (wrap_add x y z hz)

theorem sub {ty : UScalarTy} (x y : UScalar ty) :
    Refines id (UScalar.sub x y) (ok (UScalar.wrapping_sub x y)) := by
  intro z hz
  exact congrArg ok (wrap_sub x y z hz)

theorem mul {ty : UScalarTy} (x y : UScalar ty) :
    Refines id (UScalar.mul x y) (ok (UScalar.wrapping_mul x y)) := by
  intro z hz
  exact congrArg ok (wrap_mul x y z hz)

#print axioms bind
#print axioms refl
#print axioms pure
#print axioms wrap_add
#print axioms wrap_sub
#print axioms wrap_mul
#print axioms add
#print axioms sub
#print axioms mul
end R1Z.ProverCommitWrapping47
