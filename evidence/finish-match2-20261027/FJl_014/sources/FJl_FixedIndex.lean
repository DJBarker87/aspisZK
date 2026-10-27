import R1FixedWidthDecoder
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.FJl_FixedIndex
/-- Symbolic coordinate inversion of a fixed-width decoder; no concrete list
of 26 or 4 decodings is evaluated by the kernel. -/
theorem read {B A : Type} (d : List B → Option A) (k n : Nat)
    (bytes : List B) (xs : Fin n → A)
    (run : FixedWidthDecoder.decode d k n bytes=some xs) (j : Fin n) :
    d ((bytes.drop (k*j.val)).take k)=some (xs j) := by
  induction n generalizing bytes with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [FixedWidthDecoder.decode,Option.bind_eq_bind] at run
    cases h0 : d (bytes.take k) with
    | none => simp only [h0,Option.bind_none,reduceCtorEq] at run
    | some x =>
      cases ht : FixedWidthDecoder.decode d k n (bytes.drop k) with
      | none => simp only [h0,ht,Option.bind_some,Option.bind_none,reduceCtorEq] at run
      | some tail =>
        simp only [h0,ht,Option.bind_some,Option.pure_def,Option.some.injEq] at run
        subst xs
        cases j using Fin.cases with
        | zero => simpa using h0
        | succ j =>
          have h := ih (bytes.drop k) tail ht j
          simpa only [List.drop_drop,Fin.cons_succ,Fin.val_succ,Nat.mul_add,Nat.mul_one,
            Nat.add_comm] using h
#print axioms read
end AspisR1.FJl_FixedIndex
