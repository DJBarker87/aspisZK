import ShiftedRowPrefix
import CausalOrderedRelation

/-! Causal shifted-row -> image -> compact relation -> ordered query proof.
This composes actual constructed field functionals, not an arbitrary game
with supplied discrepancy identities. It is conditional on the displayed
pre-kappa anchor/support and is not acceptance-to-anchor recovery. -/
set_option autoImplicit false
namespace AspisV8.CausalShiftedRows
open Finset Polynomial
open AspisV8.JointImageGame AspisV8.CausalOrderedRelation AspisV8.ShiftedRowPrefix
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- Rows/anchor/oracle are fixed before kappa. Only the prover strategy may
depend on kappa; its type then enforces tau/alpha0/query/rho/tail order. -/
noncomputable def probability {D B : Finset K} {q : ℕ} (rows : Rows (K := K))
    (hq : rows.quarter*4=1) (oracle : FixedOracle D B rows.referenceQ)
    (strategy : K → Strategy D q) (A G : Finset K) : ℚ :=
  avg G (fun kappa =>
    CausalOrderedRelation.probability (rows.before kappa) hq oracle (strategy kappa) A G)

/-- All four actual ordinary errors are retained, including inactive error.
Image validity makes the tau augmentation contribute zero to the reference
dot; it does not erase the check or condition on an image challenge outcome.
The four relation repairs are charged once in this whole causal game. -/
theorem wrong_rows_bound {D B : Finset K} {q : ℕ} (rows : Rows (K := K))
    (hq : rows.quarter*4=1) (oracle : FixedOracle D B rows.referenceQ)
    (strategy : K → Strategy D q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hpos : 0<q) (hcount : q≤D.card)
    (image1 : rows.referenceQ ⟨1023, by decide⟩=0)
    (image2 : rows.b*rows.referenceQ ⟨1022, by decide⟩-
      rows.c*rows.referenceQ ⟨1021, by decide⟩=0)
    (wrong : rows.errors≠0) :
    probability rows hq oracle strategy A G ≤
      ((q:ℚ)+3)/G.card+24/A.card+((B.card+255).choose q : ℚ)/D.card.choose q := by
  have h := avg_polynomial G hg rows.errorPolynomial
    (ShiftedRowPrefix.error_nonzero rows wrong) 3 (ShiftedRowPrefix.error_degree rows)
    (fun kappa => CausalOrderedRelation.probability
      (rows.before kappa) hq oracle (strategy kappa) A G)
    ((q:ℚ)/G.card+24/A.card+((B.card+255).choose q : ℚ)/D.card.choose q)
    (by positivity)
    (fun kappa _ => CausalOrderedRelation.probability_unit
      (rows.before kappa) hq oracle (strategy kappa) A G ha hg hcount)
    (by
      intro kappa _ nonzero
      apply CausalOrderedRelation.image_valid_wrong_bound
        (rows.before kappa) hq oracle (strategy kappa) A G ha hg hpos hcount
      · exact image1
      · exact image2
      · rw [before_prior]
        exact nonzero)
  change avg _ _ ≤ _
  convert h using 1 <;> ring

#print axioms probability
#print axioms wrong_rows_bound
end AspisV8.CausalShiftedRows
