import AspisR1.PoseidonSelectorsSource
import PoseidonInternalPairExact
import PoseidonCandidateProjectedWrapperSuccessV8
import PoseidonSamePointResidualModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.PoseidonCandidateProjectedBoxedPointExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (cell)
open AspisR1.PoseidonCandidateProjectedWrapperFactor
open AspisR1.PoseidonCandidateProjectedWrapperSuccess
open AspisR1.PoseidonSamePointResidualModel

abbrev QM := field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) := ∀ i : Fin n.val, Canonical (a.val[i.val])
abbrev State := AspisR1.PoseidonFullRoundCellStep.State
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := AspisR1.PoseidonSelectorsSource.Output
abbrev Packed := Array QM 4#usize
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

private def localAt (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

/-- The actual boxed-point candidate path reaches the scalar residual model.
The selector source and internal-pair source calls are derived here. The only
remaining call/model premises are for the leading and full packed branches. -/
theorem boxed_candidate_scalar_residual
    (openings : Openings) (point : Array QM 10#usize)
    (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors)
    (leading full : Packed)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput)
    (hleadingCall : state_only_poseidon.leading_pair_packed openings = .ok leading)
    (hfullCall : state_only_poseidon.interpolated_full_pair_packed openings.z selectorInput.low = .ok full)
    (hleadingCanonical : CanonicalArray leading) (hfullCanonical : CanonicalArray full)
    :
    ∃ selectors : Selectors, ∃ internal : State,
    ∃ leadingLow fullLow internalLow : QM, ∃ weights : Array QM 3#usize,
    ∃ out : Packed,
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      (∀ j : Fin 16, Decode (cell internal j) =
        R0P.poseidonInterpolatedInternalPair (fun i => Decode (cell openings.z i))
          (fun i => Decode (cell selectors.local i)) j) ∧
      weights = Array.make 3#usize [leadingLow,fullLow,internalLow] ∧
      Decode leadingLow = R0P.g2Low (pointSelector point) 0 ∧
      Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow (R0P.g2Low (pointSelector point)) ∧
      Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow (R0P.g2Low (pointSelector point)) ∧
      candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, Canonical (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out g) =
        AspisR1.PoseidonSamePointArray.model openings point internal leading full g := by
  obtain ⟨selectors,hselectors,hblockCan,hlocalCan,hlocals,hblockModel,hlowModel⟩ :=
    AspisR1.PoseidonSelectorsSource.boxed_success point selectorInput hpoint hbox
  have hlocalState : AspisR1.PoseidonFullRoundCellStep.CanonicalState selectors.local := by
    intro j
    exact hlocalCan j
  obtain ⟨internal,hinternalCall,hinternalCan,hinternalModel⟩ :=
    AspisR1.PoseidonInternalPairExact.source_success openings.z selectors.local hopenZ hlocalState
  have hsuccessor : ∀ i : Fin 16, Canonical
      (openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt)) := by
    intro i
    exact hopenSucc i
  have hinternal : ∀ i : Fin 16, Canonical
      (internal.val[i.val]'(by simpa [internal.property] using i.isLt)) := by
    intro i
    exact hinternalCan i
  have hleadingCan : ∀ (i : Usize) (hi : i.val < 4), Canonical
      (leading.val[i.val]'(by simpa [leading.property] using hi)) := by
    intro i hi
    exact hleadingCanonical ⟨i.val, by simpa using hi⟩
  have hfullCan : ∀ (i : Usize) (hi : i.val < 4), Canonical
      (full.val[i.val]'(by simpa [full.property] using hi)) := by
    intro i hi
    exact hfullCanonical ⟨i.val, by simpa using hi⟩
  have hfullCall' : state_only_poseidon.interpolated_full_pair_packed openings.z selectors.local = .ok full := by
    rw [hlocals]
    exact hfullCall
  obtain ⟨leadingLow,fullLow,internalLow,weights,out,hweights,hleadingLow,hfullLow,
      hinternalLow,hout,houtCan,houtModel⟩ :=
    AspisR1.PoseidonCandidateProjectedWrapperSuccess.success_from_component_success
      openings selectors leading full internal hblockCan hlocalCan hsuccessor hinternal
      hleadingCan hfullCan hleadingCall hfullCall' hinternalCall
  have hlow : (fun j : Fin 16 => Decode (localAt selectors.local j)) =
      R0P.g2Low (pointSelector point) := by
    funext j
    have hj : j.val < (16#usize).val := by simpa using j.isLt
    have h := hlowModel j
    dsimp only [AspisR1.SelectorExpansionCorrectness.decodedArray,
      AspisR1.SelectorExpansionCorrectness.decodedAt] at h
    rw [dif_pos hj] at h
    change Decode (localAt selectors.local j) = R0P.g2Low (pointSelector point) j at h
    exact h
  have hlocalLow : (fun j : Fin 16 => Decode (cell selectors.local j)) =
      (fun j => Decode (localAt selectors.local j)) := by
    funext j
    rfl
  have hblockModel' : AspisR1.PoseidonClosure2ArrayExact.Decode selectors.block =
      R0P.g2SumHigh (pointSelector point) 0 57 (by omega) := by
    change Decode selectors.block = _
    exact hblockModel
  have hleadingLowValue : Decode leadingLow = R0P.g2Low (pointSelector point) 0 := by
    change Decode leadingLow = Decode (localAt selectors.local 0) at hleadingLow
    calc
      Decode leadingLow = Decode (localAt selectors.local 0) := hleadingLow
      _ = R0P.g2Low (pointSelector point) 0 := congrFun hlow 0
  have hleadingLowModel : AspisR1.PoseidonClosure2ArrayExact.Decode leadingLow =
      R0P.g2Low (pointSelector point) 0 := by
    change Decode leadingLow = _
    exact hleadingLowValue
  have hfullLowValue : Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
      (R0P.g2Low (pointSelector point)) := by
    change Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
      (fun j => Decode (localAt selectors.local j)) at hfullLow
    calc
      Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
        (fun j => Decode (localAt selectors.local j)) := hfullLow
      _ = AspisR1.PoseidonExplicitLowWeightFold.fullLow (R0P.g2Low (pointSelector point)) :=
        congrArg AspisR1.PoseidonExplicitLowWeightFold.fullLow hlow
  have hfullLowModel : AspisR1.PoseidonClosure2ArrayExact.Decode fullLow =
      AspisR1.PoseidonExplicitLowWeightFold.fullLow (R0P.g2Low (pointSelector point)) := by
    change Decode fullLow = _
    exact hfullLowValue
  have hinternalLowValue : Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
      (R0P.g2Low (pointSelector point)) := by
    change Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
      (fun j => Decode (localAt selectors.local j)) at hinternalLow
    calc
      Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
        (fun j => Decode (localAt selectors.local j)) := hinternalLow
      _ = AspisR1.PoseidonExplicitLowWeightFold.internalLow (R0P.g2Low (pointSelector point)) :=
        congrArg AspisR1.PoseidonExplicitLowWeightFold.internalLow hlow
  have hinternalLowModel : AspisR1.PoseidonClosure2ArrayExact.Decode internalLow =
      AspisR1.PoseidonExplicitLowWeightFold.internalLow (R0P.g2Low (pointSelector point)) := by
    change Decode internalLow = _
    exact hinternalLowValue
  refine ⟨selectors,internal,leadingLow,fullLow,internalLow,weights,out,
    hselectors,hinternalCall,?_,hweights,hleadingLowModel,hfullLowModel,hinternalLowModel,
    hout,houtCan,?_⟩
  · intro j
    exact hinternalModel j
  · intro g
    have hclosure := houtModel g
    rw [hweights, AspisR1.PoseidonClosure2ArrayExact.model_three] at hclosure
    have hclosureSame : AspisR1.PoseidonClosure2ArrayExact.model openings internal
        selectors.block (Array.make 3#usize [leadingLow,fullLow,internalLow]) leading full g =
        AspisR1.PoseidonSamePointArray.model openings point internal leading full g := by
      rw [AspisR1.PoseidonClosure2ArrayExact.model_three]
      unfold AspisR1.PoseidonSamePointArray.model
      rw [hblockModel', hleadingLowModel, hfullLowModel, hinternalLowModel]
    exact hclosure.trans hclosureSame

#print axioms boxed_candidate_scalar_residual
end AspisR1.PoseidonCandidateProjectedBoxedPointExact
