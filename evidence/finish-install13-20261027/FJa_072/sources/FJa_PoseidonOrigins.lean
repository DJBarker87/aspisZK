import FIq_Native07
import FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PoseidonOrigins
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := state_only_poseidon.StateOnlyPoseidonSelectors
abbrev NP := field.PreparedQm31Multiplier
def fullFold (s : Selectors) : Result NQ := do
  let ii ← Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    (Array.make 3#usize [1#usize,9#usize,10#usize])
  core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
    ii field.QM31.ZERO s
def internalFold (s : Selectors) : Result NQ := do
  let ri ← core.ops.range.RangeInclusive.new 2#usize 8#usize
  core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold core.iter.range.StepUsize
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
    ri field.QM31.ZERO s
/-- Reached typed cuts from the SAME ORIGINAL evaluator call; no component
success is an extra hypothesis. This alone claims no component value. -/
theorem reached (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    ∃ (leadingLow fullLow internalLow : NQ) (leading full : Array NQ 4#usize)
      (internal : Array NQ 16#usize) (prepared : Array NP 3#usize) (block : NP),
      Array.index_usize s.local 0#usize=ok leadingLow ∧
      fullFold s=ok fullLow ∧ internalFold s=ok internalLow ∧
      state_only_poseidon.leading_pair_packed o=ok leading ∧
      state_only_poseidon.interpolated_full_pair_packed o.z s.local=ok full ∧
      state_only_poseidon.interpolated_internal_pair o.z s.local=ok internal ∧
      core.array.Array.map (BuiltinFnMut NQ NP)
        (Array.make 3#usize [leadingLow,fullLow,internalLow]) field.PreparedQm31Multiplier.new=ok prepared ∧
      field.PreparedQm31Multiplier.new s.block=ok block ∧
      array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
        state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO (o,internal,block,prepared,leading,full)=ok out := by
  unfold state_only_poseidon.evaluate_state_only_poseidon_oracle_projected at run
  obtain ⟨leadingLow,h0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨ii,hii,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨fullLow,hfullLow,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨ri,hri,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨internalLow,hinternalLow,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨leading,hleading,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨full,hfull,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨internal,hinternal,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨prepared,hprepared,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨block,hblock,run⟩ := FIv_Map.bind_success _ _ _ run
  refine ⟨leadingLow,fullLow,internalLow,leading,full,internal,prepared,block,h0,?_,?_,hleading,hfull,hinternal,hprepared,hblock,run⟩
  · unfold fullFold
    rw [hii]
    exact hfullLow
  · unfold internalFold
    rw [hri]
    exact hinternalLow
#print axioms reached
end AspisR1.FJa_PoseidonOrigins
end
