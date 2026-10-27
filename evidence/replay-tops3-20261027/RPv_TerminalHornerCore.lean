-- Generic historical Horner definitions/proofs reused with separate module framing.
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace AspisR1.TerminalHornerCore
open scoped BigOperators
variable {F : Type*} [Field F]

def sourceMixHorner (x : F) (cs : List F) : F :=
  cs.reverse.foldl (fun out c => out*x+c) 0

theorem sourceMixHorner_cons (x c : F) (cs : List F) :
    sourceMixHorner x (c::cs) = sourceMixHorner x cs * x + c := by
  simp [sourceMixHorner, List.reverse_cons, List.foldl_append]

theorem sourceMixHorner_eq_sum (n : ℕ) (cs : Fin n → F) (x : F) :
    sourceMixHorner x (List.ofFn cs) = ∑ i, cs i * x^i.val := by
  induction n with
  | zero => simp [sourceMixHorner]
  | succ n ih =>
    rw [List.ofFn_succ, sourceMixHorner_cons, ih]
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    simp only [← mul_assoc, ← Finset.sum_mul]
    exact add_comm _ _

#print axioms sourceMixHorner_cons
#print axioms sourceMixHorner_eq_sum
end AspisR1.TerminalHornerCore
