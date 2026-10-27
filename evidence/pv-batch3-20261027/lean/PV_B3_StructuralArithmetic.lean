import Aeneas.Std
namespace PV_B3_StructuralArithmetic
open Aeneas Aeneas.Std Result
set_option autoImplicit false
-- Abstract error-preserving ordered traversal, used for fixed arity copies.
def walk {S I : Type} (step : S → I → Result S) : List I → S → Result S
  | [], s => ok s
  | i::is, s => do let next ← step s i; walk step is next

theorem three {S I : Type} (step : S → I → Result S) (s : S) (a b c : I) :
    walk step [a,b,c] s = (do
      let s1 ← step s a
      let s2 ← step s1 b
      step s2 c) := by
  simp only [walk, bind_tc_ok, bind_tc_pure]

theorem append {S I : Type} (step : S → I → Result S) (xs ys : List I) (s : S) :
    walk step (xs++ys) s = (do let next ← walk step xs s; walk step ys next) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.cons_append,walk,ih]
    cases h : step s i <;> rfl

theorem lifted_capture {P W I V : Type} (body : P → W → I → Result V)
    (p : P) (w : W) (i : I) :
    (fun j => body p w j) i = body p w i := rfl

#print axioms three
#print axioms append
#print axioms lifted_capture
end PV_B3_StructuralArithmetic
