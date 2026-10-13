import R0.OpeningWeights
import R1D18PointWeights
import Lean.Elab.Tactic.Omega

/-! Arithmetic alignment of the R0 Boolean opening weights with the D18 row
and tensor point products. These identities do not claim correspondence with
the Rust implementation or protocol semantics. -/

set_option autoImplicit false

namespace AspisR1

open scoped BigOperators

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- The explicit coordinate reversal used by `R0P.SemSource.toR0`. -/
def reversePoint (p : Fin 10 → K) : Fin 10 → K :=
  fun b => p ⟨9 - b.val, by have hb := b.isLt; omega⟩

private theorem rowEquiv_symm_apply (j : Fin 1024) :
    rowEquiv.symm j = rowEquiv j := by
  apply rowEquiv.injective
  rw [rowEquiv.apply_symm_apply]
  exact (row_involutive j).symm

theorem coeffWeight_eq_rowPoint (p : Fin 10 → K) (j : Fin 1024) :
    AspisR0.Opening.coeffWeight rowEquiv
      (AspisR0.Opening.eqWeight (reversePoint p)) j = rowPoint p j := by
  rw [AspisR0.Opening.coeffWeight, rowEquiv_symm_apply]
  rfl

theorem coeffWeight_eq_tensorPoint (p : Fin 10 → K) (j : Fin 1024) :
    AspisR0.Opening.coeffWeight rowEquiv
      (AspisR0.Opening.eqWeight (reversePoint p)) j = tensorPoint p j := by
  calc
    AspisR0.Opening.coeffWeight rowEquiv
        (AspisR0.Opening.eqWeight (reversePoint p)) j = rowPoint p j :=
      coeffWeight_eq_rowPoint p j
    _ = tensorPoint p j := rowPoint_eq_tensorPoint p j

theorem dot_tensorPoint_eq_openingWeight
    (p : Fin 10 → K) (m : Fin 1024 → K) :
    AspisR0.RoundNormalization.dot (tensorPoint p) m =
      AspisR0.RoundNormalization.dot
        (AspisR0.Opening.eqWeight (reversePoint p))
        (fun r => m (rowEquiv r)) := by
  calc
    AspisR0.RoundNormalization.dot (tensorPoint p) m =
        AspisR0.RoundNormalization.dot
          (AspisR0.Opening.coeffWeight rowEquiv
            (AspisR0.Opening.eqWeight (reversePoint p))) m := by
          congr 1
          funext j
          exact (coeffWeight_eq_tensorPoint p j).symm
    _ = AspisR0.RoundNormalization.dot
        (AspisR0.Opening.eqWeight (reversePoint p))
        (fun r => m (rowEquiv r)) :=
      AspisR0.Opening.dot_coeffWeight_left rowEquiv
        (AspisR0.Opening.eqWeight (reversePoint p)) m

theorem coeffWeight_indicator_eq_rowIndicator
    (I : Finset (Fin 1024)) (j : Fin 1024) :
    AspisR0.Opening.coeffWeight rowEquiv (AspisR0.Opening.indicator I) j =
      if row j ∈ I then (1 : K) else 0 := by
  change AspisR0.Opening.indicator (K := K) I (rowEquiv.symm j) = _
  rw [rowEquiv_symm_apply]
  rfl

theorem dot_coeffWeight_indicator_rows
    (I : Finset (Fin 1024)) (m : Fin 1024 → K) :
    AspisR0.RoundNormalization.dot
      (AspisR0.Opening.coeffWeight rowEquiv (AspisR0.Opening.indicator I)) m =
      ∑ r ∈ I, m (rowEquiv r) :=
  AspisR0.Opening.dot_coeffWeight_indicator rowEquiv I m

#print axioms rowEquiv_symm_apply
#print axioms coeffWeight_eq_rowPoint
#print axioms coeffWeight_eq_tensorPoint
#print axioms dot_tensorPoint_eq_openingWeight
#print axioms coeffWeight_indicator_eq_rowIndicator
#print axioms dot_coeffWeight_indicator_rows

end AspisR1
