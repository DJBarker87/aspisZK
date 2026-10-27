import RPv_FJa_MapRelation
import RPv_FJh_Base
set_option autoImplicit false
namespace AspisR1.FJh_MapCells
open Aeneas Aeneas.Std Result
theorem get {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (rel : List.Forall₂ R xs ys) (i : Nat) (hx : i<xs.length) (hy : i<ys.length) :
    R (xs[i]'hx) (ys[i]'hy) := by
  induction rel generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab hrel ih =>
    cases i with
    | zero => exact hab
    | succ i => exact ih i (by simpa using hx) (by simpa using hy)
#print axioms get
end AspisR1.FJh_MapCells
