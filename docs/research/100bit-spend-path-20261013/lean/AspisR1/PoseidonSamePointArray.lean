import AspisR1.PoseidonClosure2ArrayExact
import AspisR1.PoseidonBoxedPreparedInputs

/-! Factored selector/preparation/output dataflow. The intervening source
leading/full/internal evaluations remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.PoseidonSamePointArray
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

def at3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
def prepAt3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
def lowAt (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def source (openings : Openings) (selectors : Selectors)
    (internalArray : Array QM 16#usize) (leading full : Array QM 4#usize) :
    Result (Array QM 4#usize) := do
  let (ops,weightsPrepared,blockPrepared) ← AspisR1.PoseidonBoxedPreparedInputs.source selectors
  array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
    AspisR1.PoseidonClosure2ArrayExact.Callback field.QM31.ZERO
    (openings,internalArray,blockPrepared,weightsPrepared,leading,full)

def model (openings : Openings) (point : Array QM 10#usize)
    (internalArray : Array QM 16#usize) (leading full : Array QM 4#usize) (i : Fin 4) : Exact :=
  R0P.g2SumHigh (pointSelector point) 0 57 (by omega) *
    (R0P.g2Low (pointSelector point) 0 *
        (AspisR1.PoseidonGroupSliceModel.packedGroup openings.succ_z i -
          Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 leading i)) +
      AspisR1.PoseidonExplicitLowWeightFold.fullLow (R0P.g2Low (pointSelector point)) *
        (AspisR1.PoseidonGroupSliceModel.packedGroup openings.succ_z i -
          Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 full i)) +
      AspisR1.PoseidonExplicitLowWeightFold.internalLow (R0P.g2Low (pointSelector point)) *
        (AspisR1.PoseidonGroupSliceModel.packedGroup openings.succ_z i -
          AspisR1.PoseidonGroupSliceModel.packedGroup internalArray i))

/-- All selector, low-weight, multiplier and pack-input equations are derived
from source calls on the same boxed point and actual arrays. -/
theorem source_success
    (openings : Openings) (point : Array QM 10#usize) (selectors : Selectors)
    (internalArray : Array QM 16#usize) (leading full : Array QM 4#usize)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hsucc : CanonicalArray openings.succ_z) (hinternal : CanonicalArray internalArray)
    (hleading : CanonicalArray leading) (hfull : CanonicalArray full) :
    ∃ out : Array QM 4#usize, source openings selectors internalArray leading full = .ok out ∧
      CanonicalArray out ∧ ∀ i : Fin 4,
        Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out i) =
          model openings point internalArray leading full i := by
  obtain ⟨ops,hops,hblockCan,hlocalCan,hlocals,hblockModel,hlowModel⟩ :=
    AspisR1.PoseidonSelectorsSource.boxed_success point selectors hpoint hbox
  obtain ⟨leadingLow,fullLow,internalLow,rawWeights,weightsPrepared,hweights,hraw,
    hleadingCan,hfullCan,hinternalCan,hp0,hp1,hp2,hleadingDec,hfullDec,hinternalDec⟩ :=
    AspisR1.PoseidonActualPreparedWeights.source_success ops.«local» hlocalCan
  subst rawWeights
  let weights : Array QM 3#usize := Array.make 3#usize [leadingLow,fullLow,internalLow]
  obtain ⟨blockPrepared,hblockNew,hblockPrepared⟩ :=
    AspisR1.ExtractedMaskPreparedState.current_prepared_new ops.block hblockCan
  have hcanonWeights : ∀ i : Fin 3, Canonical (at3 weights i) := by
    intro i
    fin_cases i <;> simp [at3,weights,Array.make,hleadingCan,hfullCan,hinternalCan]
  change PreparedFor (prepAt3 weightsPrepared 0) leadingLow at hp0
  change PreparedFor (prepAt3 weightsPrepared 1) fullLow at hp1
  change PreparedFor (prepAt3 weightsPrepared 2) internalLow at hp2
  simp only [prepAt3,show (0 : Fin 3).val = 0 from rfl] at hp0
  simp only [prepAt3,show (1 : Fin 3).val = 1 from rfl] at hp1
  simp only [prepAt3,show (2 : Fin 3).val = 2 from rfl] at hp2
  have hpreparedWeights : ∀ i : Fin 3, PreparedFor (prepAt3 weightsPrepared i) (at3 weights i) := by
    intro i
    fin_cases i
    · simpa only [prepAt3,at3,weights,Array.make,List.getElem_cons_zero] using hp0
    · simpa only [prepAt3,at3,weights,Array.make,List.getElem_cons_succ,List.getElem_cons_zero] using hp1
    · simpa only [prepAt3,at3,weights,Array.make,List.getElem_cons_succ,List.getElem_cons_zero] using hp2
  have hleadingAll : ∀ (i : Usize) (hi : i.val < 4), Canonical
      (leading.val[i.val]'(by simpa [leading.property] using hi)) := by
    intro i hi
    exact hleading ⟨i.val,by simpa using hi⟩
  have hfullAll : ∀ (i : Usize) (hi : i.val < 4), Canonical
      (full.val[i.val]'(by simpa [full.property] using hi)) := by
    intro i hi
    exact hfull ⟨i.val,by simpa using hi⟩
  obtain ⟨out,harray,houtCan,houtModel⟩ :=
    AspisR1.PoseidonClosure2ArrayExact.source_success openings internalArray
      blockPrepared ops.block weightsPrepared weights leading full
      hblockCan hblockPrepared hcanonWeights hpreparedWeights hsucc hinternal hleadingAll hfullAll
  have hinputs : AspisR1.PoseidonBoxedPreparedInputs.source selectors =
      .ok (ops,weightsPrepared,blockPrepared) := by
    simp only [AspisR1.PoseidonBoxedPreparedInputs.source,hops,bind_tc_ok,hweights,hblockNew]
  have hlow : (fun j : Fin 16 => Decode (lowAt ops.«local» j)) =
      R0P.g2Low (pointSelector point) := by
    funext j
    have hj : j.val < (16#usize).val := by simpa using j.isLt
    have h := hlowModel j
    dsimp only [AspisR1.SelectorExpansionCorrectness.decodedArray,
      AspisR1.SelectorExpansionCorrectness.decodedAt] at h
    rw [dif_pos hj] at h
    change Decode (lowAt ops.«local» j) = R0P.g2Low (pointSelector point) j at h
    exact h
  change Decode leadingLow = Decode (lowAt ops.«local» 0) at hleadingDec
  change Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
    (fun j => Decode (lowAt ops.«local» j)) at hfullDec
  change Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
    (fun j => Decode (lowAt ops.«local» j)) at hinternalDec
  have hleadingModel : Decode leadingLow = R0P.g2Low (pointSelector point) 0 := by
    rw [hleadingDec]
    exact congrFun hlow 0
  rw [hlow] at hfullDec hinternalDec
  change Decode ops.block = R0P.g2SumHigh (pointSelector point) 0 57 (by omega) at hblockModel
  refine ⟨out,?_,houtCan,?_⟩
  · simpa only [source,hinputs,bind_tc_ok,Aeneas.Std.uncurry_apply_pair,AspisR1.PoseidonClosure2ArrayExact.run] using harray
  · intro i
    have hmodel := houtModel i
    change _ = AspisR1.PoseidonClosure2ArrayExact.model openings internalArray ops.block
      (Array.make 3#usize [leadingLow,fullLow,internalLow]) leading full i at hmodel
    rw [AspisR1.PoseidonClosure2ArrayExact.model_three] at hmodel
    change Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out i) =
      Decode ops.block * (Decode leadingLow * _ + Decode fullLow * _ + Decode internalLow * _) at hmodel
    rw [hblockModel,hleadingModel,hfullDec,hinternalDec] at hmodel
    have hdecodeFn : AspisR1.PoseidonClosure2ArrayExact.Decode = Decode := rfl
    rw [hdecodeFn] at hmodel
    unfold model
    refine hmodel.trans ?_
    apply congrArg₂ (fun (a b : Exact) => a * b)
    · apply congrArg (fun (h : 0 + 57 ≤ 64) =>
        R0P.g2SumHigh (pointSelector point) 0 57 h)
      exact Subsingleton.elim _ _
    · rfl

#print axioms source_success
end
end AspisR1.PoseidonSamePointArray
