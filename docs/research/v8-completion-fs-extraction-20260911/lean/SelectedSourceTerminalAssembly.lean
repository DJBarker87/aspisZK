import CausalSourcePolynomialTrace
import SelectedConcreteRowLanes
import AspisFormal.V5ConstraintLaneBatching

/-! Exact algebraic assembly used by
`pair_forest_semantic_terminal::{composition_parts,terminal_parts}`.

This leaf closes the 4+24+1 reverse-Horner order and the equality/helper/
inactive-helper assembly.  It deliberately stops before claiming that the
Rust Poseidon, semantic, Copy, helper, active-mask or hiding evaluators equal
the corresponding mathematical inputs below.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedSourceTerminalAssembly
open scoped BigOperators
open Polynomial
open AspisV5ConstraintLaneBatching
open AspisV5FriConcreteEncoderApplicability
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedSemanticHelperAggregation
open AspisV8.SelectedSemanticTerminalAlternative

variable {K : Type*} [Field K] [DecidableEq K]

/-- A reverse iterator Horner loop over `n` ascending-power coefficients is
the coefficient polynomial plus the supplied accumulator at power `n`. -/
theorem reverseHorner_ofFn {n : Nat} (values : Fin n → K)
    (theta accumulator : K) :
    reverseHorner (List.ofFn values) theta accumulator =
      (monomialPolynomial values).eval theta + theta ^ n * accumulator := by
  induction n with
  | zero => simp [reverseHorner, monomialPolynomial]
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [reverseHorner, List.foldr_cons]
      have htail := ih (fun i => values i.succ)
      change List.foldr (fun lane current => theta * current + lane) accumulator
          (List.ofFn fun i => values i.succ) = _ at htail
      rw [htail]
      simp only [monomialPolynomial, Polynomial.eval_finsetSum,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
        Fin.val_succ, pow_succ]
      simp only [mul_add, Finset.mul_sum]
      ring

/-- Literal spelling of the source's two loops: semantic lanes are folded
into Copy first, then Poseidon lanes are folded around that accumulator. -/
def sourceComposition (lanes : RowLanes K) (theta : K) : K :=
  reverseHorner (List.ofFn lanes.poseidon) theta
    (reverseHorner (List.ofFn lanes.semantic) theta lanes.copy)

/-- The literal 4+24+1 source loops are exactly the selected degree-28 row
polynomial evaluation, including Copy at exponent 28. -/
theorem sourceComposition_eq_rowPolynomial_eval
    (lanes : RowLanes K) (theta : K) :
    sourceComposition lanes theta = (rowPolynomial lanes).eval theta := by
  rw [sourceComposition, reverseHorner_ofFn, reverseHorner_ofFn,
    selected_row_eval]

/-- The ten-coordinate loop used by Rust's `equality_value`, presented with
the same factor formula.  Starting from one instead of spelling out the first
factor is observationally identical in a field and makes the finite traversal
explicit. -/
def sourceEqualityLoop (left right : Fin 10 → K) : K :=
  (List.ofFn fun coordinate =>
    1 - left coordinate - right coordinate +
      left coordinate * right coordinate + left coordinate * right coordinate).prod

/-- The source's ten-factor traversal is the finite product used by the V8
semantic model; no equality-value correspondence is left as a premise. -/
theorem sourceEqualityLoop_eq_sourceEqualityValue
    (left right : Fin 10 → K) :
    sourceEqualityLoop left right = sourceEqualityValue left right := by
  simp [sourceEqualityLoop, sourceEqualityValue, Fin.prod_univ_succ]

/-- Literal field assembly in `terminal_parts` after its component evaluators
have returned. -/
def sourceOriginal (lanes : RowLanes K) (helper active : K)
    (theta : K) (zerocheckPoint point : Fin 10 → K) (mu : K) : K :=
  sourceEqualityValue zerocheckPoint point * sourceComposition lanes theta +
    mu * helper + mu ^ 2 * ((1 - active) * helper)

/-- On every Boolean trace row, the source terminal assembly is exactly the
Boolean restriction table used by the recovery argument.  This proves the
assembly itself; it does not infer off-domain evaluation from this equality. -/
theorem sourceOriginal_booleanRow_eq_realTable
    (lanes : Fin 1024 → RowLanes K) (helper active : Fin 1024 → K)
    (theta : K) (zerocheckPoint : Fin 10 → K) (mu : K) (row : Fin 1024) :
    sourceOriginal (lanes row) (helper row) (active row) theta zerocheckPoint
        (booleanTracePoint row) mu =
      realTable lanes helper active theta zerocheckPoint mu row := by
  rw [sourceOriginal, sourceComposition_eq_rowPolynomial_eval,
    sourceEqualityValue_booleanTracePoint]
  rfl

/-- The final source line is a linear masking composition.  The still-open
source theorem must identify `maskValue` with the literal selected hiding
polynomial and `sourceOriginal`'s inputs with the actual callback outputs. -/
def sourceMaskedTerminal (maskValue original eta : K) : K :=
  maskValue + eta * original

theorem sourceMaskedTerminal_eq (maskValue eta : K)
    (lanes : RowLanes K) (helper active : K) (theta : K)
    (zerocheckPoint point : Fin 10 → K) (mu : K) :
    sourceMaskedTerminal maskValue
      (sourceOriginal lanes helper active theta zerocheckPoint point mu) eta =
      maskValue + eta *
        (sourceEqualityValue zerocheckPoint point * sourceComposition lanes theta +
          mu * helper + mu ^ 2 * ((1 - active) * helper)) := by
  rfl

#print axioms reverseHorner_ofFn
#print axioms sourceComposition_eq_rowPolynomial_eval
#print axioms sourceEqualityLoop_eq_sourceEqualityValue
#print axioms sourceOriginal_booleanRow_eq_realTable
#print axioms sourceMaskedTerminal_eq
end AspisV8Completion.SelectedSourceTerminalAssembly
