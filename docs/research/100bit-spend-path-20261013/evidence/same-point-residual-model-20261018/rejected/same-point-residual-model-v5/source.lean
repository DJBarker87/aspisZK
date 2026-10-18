import AspisR1.PoseidonSamePointArray
import AspisR1.PoseidonResidualPacking
import PoseidonResidualFieldTransport
import ExtractedMaskSemanticBridgeConcrete

/-! The already-checked selector/preparation/output dataflow computes the
retained R0P scalar residual, provided its three incoming round arrays have
their specified models. These premises name the remaining caller boundary;
no source success or packing injectivity is assumed. -/
set_option autoImplicit false
namespace AspisR1.PoseidonSamePointResidualModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev State := Array field.QM31 16#usize
abbrev Packed := Array field.QM31 4#usize
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev lane := AspisR1.PoseidonResidualPacking.lane
abbrev iBasis := AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
abbrev uBasis := AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis

def decodedState (state : State) : Fin 16 → Exact := fun j =>
  Decode (state.val[j.val]'(by simpa [state.property] using j.isLt))
def decodedOpenings (o : Openings) : R0P.Openings Exact :=
  ⟨decodedState o.z,decodedState o.succ_z,decodedState o.xor12_z⟩

theorem packedGroup_eq (state : State) (group : Fin 4) :
    AspisR1.PoseidonGroupSliceModel.packedGroup state group =
      R0P.poseidonPackingFormula iBasis uBasis (fun j => decodedState state (lane group j)) := by
  rfl

theorem scalar_group_pack {K : Type} [Field K]
    (o : R0P.Openings K) (block i u : K) (low : Fin 16 → K) (group : Fin 4) :
    block *
      (low 0 * (R0P.poseidonPackingFormula i u (fun j => o.succ (lane group j)) -
          R0P.poseidonPackingFormula i u (fun j => R0P.poseidonLeadingPair o.z o.xor12 (lane group j))) +
        AspisR1.PoseidonExplicitLowWeightFold.fullLow low *
          (R0P.poseidonPackingFormula i u (fun j => o.succ (lane group j)) -
            R0P.poseidonPackingFormula i u (fun j => R0P.poseidonInterpolatedFullPair o.z low (lane group j))) +
        AspisR1.PoseidonExplicitLowWeightFold.internalLow low *
          (R0P.poseidonPackingFormula i u (fun j => o.succ (lane group j)) -
            R0P.poseidonPackingFormula i u (fun j => R0P.poseidonInterpolatedInternalPair o.z low (lane group j)))) =
      R0P.poseidonPackingFormula i u (fun j => R0P.poseidonScalarResidual o block low (lane group j)) := by
  simpa only [R0P.poseidonScalarResidual,
    AspisR1.PoseidonExplicitLowWeightFold.fullLow,
    AspisR1.PoseidonExplicitLowWeightFold.internalLow,zero_add] using
      AspisR1.PoseidonResidualPacking.weighted_pack i u block (low 0)
        (AspisR1.PoseidonExplicitLowWeightFold.fullLow low)
        (AspisR1.PoseidonExplicitLowWeightFold.internalLow low)
        (fun j => o.succ (lane group j))
        (fun j => R0P.poseidonLeadingPair o.z o.xor12 (lane group j))
        (fun j => R0P.poseidonInterpolatedFullPair o.z low (lane group j))
        (fun j => R0P.poseidonInterpolatedInternalPair o.z low (lane group j))

set_option maxRecDepth 2048 in
theorem same_point_model_eq (o : Openings) (point : Array field.QM31 10#usize)
    (internalArray : State) (leading full : Packed)
    (hleading : ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 leading g) =
      R0P.poseidonPackingFormula iBasis uBasis (fun j =>
        R0P.poseidonLeadingPair (decodedOpenings o).z (decodedOpenings o).xor12 (lane g j)))
    (hfull : ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 full g) =
      R0P.poseidonPackingFormula iBasis uBasis (fun j =>
        R0P.poseidonInterpolatedFullPair (decodedOpenings o).z
          (R0P.g2Low (pointSelector point)) (lane g j)))
    (hinternal : ∀ j : Fin 16, decodedState internalArray j =
      R0P.poseidonInterpolatedInternalPair (decodedOpenings o).z
        (R0P.g2Low (pointSelector point)) j)
    (group : Fin 4) :
    AspisR1.PoseidonSamePointArray.model o point internalArray leading full group =
      R0P.poseidonPackingFormula iBasis uBasis (fun j =>
        R0P.poseidonScalarResidual (decodedOpenings o)
          (R0P.g2SumHigh (pointSelector point) 0 57 (by omega))
          (R0P.g2Low (pointSelector point)) (lane group j)) := by
  have hint : decodedState internalArray =
      R0P.poseidonInterpolatedInternalPair (decodedOpenings o).z
        (R0P.g2Low (pointSelector point)) := funext hinternal
  unfold AspisR1.PoseidonSamePointArray.model
  have hdecode : AspisR1.PoseidonSamePointArray.Decode = Decode := rfl
  have hselector : AspisR1.PoseidonSamePointArray.pointSelector = pointSelector := rfl
  rw [hdecode,hselector,hleading group,hfull group]
  simp only [packedGroup_eq,hint]
  have hsucc : decodedState o.succ_z = (decodedOpenings o).succ := rfl
  rw [hsucc]
  exact scalar_group_pack (K := Exact) (decodedOpenings o)
    (R0P.g2SumHigh (pointSelector point) 0 57 (by omega)) iBasis uBasis
    (R0P.g2Low (pointSelector point)) group

#print axioms packedGroup_eq
#print axioms scalar_group_pack
#print axioms same_point_model_eq
end AspisR1.PoseidonSamePointResidualModel
