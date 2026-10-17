import AspisR1.PoseidonSelectorsSource
import AspisR1.PoseidonActualPreparedWeights

/-! Same-point source selector/preparation dataflow. These factored calls form
only the selector and multiplier inputs; the intervening leading/full/internal
source evaluations and the enclosing projected oracle remain separate. -/
set_option autoImplicit false
namespace AspisR1.PoseidonBoxedPreparedInputs
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
abbrev Prepared := field.PreparedQm31Multiplier
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev SelectorOutput := AspisR1.PoseidonSelectorsSource.Output
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

def lowAt (a : Array QM 16#usize) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
def preparedAt (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def source (selectors : Selectors) :
    Result (SelectorOutput × Array Prepared 3#usize × Prepared) := do
  let ops ← AspisR1.PoseidonSelectorsSource.source selectors
  let weights ← AspisR1.PoseidonActualPreparedWeights.source ops.«local»
  let block ← field.PreparedQm31Multiplier.new ops.block
  .ok (ops, weights, block)

/-- Actual boxed selectors derive all prepared-state invariants, rather than
assuming multiplier tables or unrelated low selector equations. -/
theorem boxed_source_success
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ (ops : SelectorOutput) (weights : Array Prepared 3#usize) (block : Prepared)
      (leadingLow fullLow internalLow : QM),
      source selectors = .ok (ops, weights, block) ∧
      AspisR1.PoseidonSelectorsSource.source selectors = .ok ops ∧
      Canonical ops.block ∧ CanonicalArray ops.«local» ∧ ops.«local» = selectors.low ∧
      PreparedFor block ops.block ∧
      PreparedFor (preparedAt weights 0) leadingLow ∧
      PreparedFor (preparedAt weights 1) fullLow ∧
      PreparedFor (preparedAt weights 2) internalLow ∧
      decode leadingLow = decode (lowAt ops.«local» 0) ∧
      decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
        (fun i => decode (lowAt ops.«local» i)) ∧
      decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
        (fun i => decode (lowAt ops.«local» i)) ∧
      decode ops.block = R0P.g2SumHigh (pointSelector point) 0 57 (by omega) ∧
      ∀ i : Fin 16, AspisR1.SelectorExpansionCorrectness.decodedArray ops.«local» i.val =
        R0P.g2Low (pointSelector point) i := by
  obtain ⟨ops,hops,hblockCan,hlocalCan,hlocals,hblockModel,hlowModel⟩ :=
    AspisR1.PoseidonSelectorsSource.boxed_success point selectors hpoint hbox
  obtain ⟨leadingLow,fullLow,internalLow,rawWeights,weights,hweights,hraw,
    hleading,hfull,hinternal,hp0,hp1,hp2,hleadingDec,hfullDec,hinternalDec⟩ :=
    AspisR1.PoseidonActualPreparedWeights.source_success ops.«local» hlocalCan
  obtain ⟨block,hnew,hprepared⟩ :=
    AspisR1.ExtractedMaskPreparedState.current_prepared_new ops.block hblockCan
  refine ⟨ops,weights,block,leadingLow,fullLow,internalLow,?_,hops,
    hblockCan,hlocalCan,hlocals,hprepared,hp0,hp1,hp2,
    hleadingDec,hfullDec,hinternalDec,hblockModel,hlowModel⟩
  simp only [source,hops,bind_tc_ok,hweights,hnew]

#print axioms boxed_source_success
end
end AspisR1.PoseidonBoxedPreparedInputs
