import NDO_JFy_PoseidonFullLow
import NDO_JFy_PoseidonInternalLow
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PoseidonPrefix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open state_only_poseidon.evaluate_state_only_poseidon_oracle_projected

def tail (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : state_only_poseidon.StateOnlyPoseidonSelectors)
    (leading_low full_low internal_low : field.QM31) : Result (Array field.QM31 4#usize) := do
  let leading ← state_only_poseidon.leading_pair_packed openings
  let full ←
    state_only_poseidon.interpolated_full_pair_packed openings.z
      selectors.«local»
  let internal ←
    state_only_poseidon.interpolated_internal_pair openings.z
      selectors.«local»
  let prepared_weights ←
    FIq_Native.core.array.Array.map (BuiltinFnMut field.QM31 field.PreparedQm31Multiplier)
      (Array.make 3#usize [ leading_low, full_low, internal_low ])
      (field.PreparedQm31Multiplier.new)
  let prepared_block ← field.PreparedQm31Multiplier.new selectors.block
  array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO (openings, internal, prepared_block, prepared_weights,
    leading, full)

theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : state_only_poseidon.StateOnlyPoseidonSelectors) (hs : canonical s.«local») :
    ∃ leading full internal,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=tail o s leading full internal ∧
    Canon leading ∧ Canon full ∧ Canon internal := by
  obtain ⟨leading,hl,hlc⟩ := JFy_ArrayTotal.read s.«local» 0#usize (by decide) hs
  obtain ⟨full,hf,hfc⟩ := JFy_PoseidonFullLow.source s hs
  obtain ⟨internal,hi,hic⟩ := JFy_PoseidonInternalLow.source s hs
  refine ⟨leading,full,internal,?_,hlc,hfc,hic⟩
  unfold state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
  rw [hl,bind_tc_ok]
  change (do
    let full ← core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold (N:=3#usize)
      closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 [1#usize,9#usize,10#usize] field.QM31.ZERO s
    let internal ← core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold core.iter.range.StepUsize
      closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 ⟨2#usize,8#usize,false⟩ field.QM31.ZERO s
    tail o s leading full internal)=tail o s leading full internal
  rw [hf,bind_tc_ok,hi,bind_tc_ok]
#print axioms source
end AspisR1.JFy_PoseidonPrefix
end
