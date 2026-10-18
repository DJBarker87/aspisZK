import R0P.Poseidon
import AspisR1.PoseidonExplicitLowWeightFold

/-! Symbolic packing only: all nonlinear round functions stay opaque. -/
set_option autoImplicit false
namespace AspisR1.PoseidonResidualPacking
variable {K : Type} [Field K]

theorem weighted_pack (i u block leadingWeight fullWeight internalWeight : K)
    (target leading full internal : Fin 4 → K) :
    block *
      (leadingWeight * (R0P.poseidonPackingFormula i u target - R0P.poseidonPackingFormula i u leading) +
        fullWeight * (R0P.poseidonPackingFormula i u target - R0P.poseidonPackingFormula i u full) +
        internalWeight * (R0P.poseidonPackingFormula i u target - R0P.poseidonPackingFormula i u internal)) =
      R0P.poseidonPackingFormula i u (fun j => block *
        (leadingWeight * (target j - leading j) + fullWeight * (target j - full j) +
          internalWeight * (target j - internal j))) := by
  unfold R0P.poseidonPackingFormula
  ring

def lane (group limb : Fin 4) : Fin 16 :=
  ⟨4 * group.val + limb.val,by have := group.isLt; have := limb.isLt; omega⟩

/-- The weighted three-branch packed formula is precisely the existing R0P
scalar residual packed in the original four-consecutive-lane order. -/
theorem poseidon_scalar_group_pack {F : Subfield K} (B : R0P.PackBasis F)
    (o : R0P.Openings K) (block : K) (low : Fin 16 → K) (group : Fin 4) :
    block *
      (low 0 *
          (R0P.pack4 B (fun j => o.succ (lane group j)) -
            R0P.pack4 B (fun j => R0P.poseidonLeadingPair o.z o.xor12 (lane group j))) +
        AspisR1.PoseidonExplicitLowWeightFold.fullLow low *
          (R0P.pack4 B (fun j => o.succ (lane group j)) -
            R0P.pack4 B (fun j => R0P.poseidonInterpolatedFullPair o.z low (lane group j))) +
        AspisR1.PoseidonExplicitLowWeightFold.internalLow low *
          (R0P.pack4 B (fun j => o.succ (lane group j)) -
            R0P.pack4 B (fun j => R0P.poseidonInterpolatedInternalPair o.z low (lane group j)))) =
      R0P.pack4 B (fun j => R0P.poseidonScalarResidual o block low (lane group j)) := by
  simpa only [R0P.pack4,R0P.poseidonScalarResidual,
    AspisR1.PoseidonExplicitLowWeightFold.fullLow,
    AspisR1.PoseidonExplicitLowWeightFold.internalLow,zero_add,
    R0P.poseidonPackingFormula] using
      weighted_pack B.i B.u block (low 0)
        (AspisR1.PoseidonExplicitLowWeightFold.fullLow low)
        (AspisR1.PoseidonExplicitLowWeightFold.internalLow low)
        (fun j => o.succ (lane group j))
        (fun j => R0P.poseidonLeadingPair o.z o.xor12 (lane group j))
        (fun j => R0P.poseidonInterpolatedFullPair o.z low (lane group j))
        (fun j => R0P.poseidonInterpolatedInternalPair o.z low (lane group j))

#print axioms weighted_pack
#print axioms poseidon_scalar_group_pack
end AspisR1.PoseidonResidualPacking
