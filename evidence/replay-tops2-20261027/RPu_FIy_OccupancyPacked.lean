import RPu_FIy_OccupancyRows
import RPu_FIy_OccupancyList
import RPu_FIx_PreweightedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyPacked
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

def input (s : Selectors) : K := FIv_NativeArray.value s.high 63*FIv_NativeArray.value s.low 9
def output (s : Selectors) : K := FIv_NativeArray.value s.high 63*FIv_NativeArray.value s.low 10

theorem value (packed out : Array NQ 24#usize) (pub : Public) (o : Openings) (s : Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes packed pub o s=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+FIx_SelectedMeaning.contribution
        (FIy_OccupancyMeaning.model (input s) (output s) (FIy_OccupancyRows.expected pub.variant)
          (FIv_NativeArray.value o.z)) 0 j.val := by
  unfold pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes at success
  rw [FIy_OccupancyRows.input,bind_tc_ok] at success
  obtain ⟨inp,hin,success⟩ := FIv_Map.bind_success _ _ _ success
  rw [FIy_OccupancyRows.output,bind_tc_ok] at success
  obtain ⟨outp,hout,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨expected,hexpected,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨occupancy,hoccupancy,success⟩ := FIv_Map.bind_success _ _ _ success
  have vin := FIw_SelectorRow.value_exact s 1017#usize inp hh hl hin
  have vout := FIw_SelectorRow.value_exact s 1018#usize outp hh hl hout
  have ve := FIy_OccupancyRows.expected_value pub.variant expected hexpected
  have vo := FIy_OccupancyMeaning.value inp outp expected o.z occupancy vin.1 vout.1 ve.1 hz hoccupancy
  have packedValue := FIx_PreweightedMeaning.value packed out 0#usize occupancy
    (FIy_OccupancyMeaning.model (decode inp) (decode outp) expected.val (FIv_NativeArray.value o.z))
    vo.2 (by decide) (by decide) hp vo.1 success
  have inValue : decode inp=input s := vin.2
  have outValue : decode outp=output s := vout.2
  refine ⟨packedValue.1,?_⟩
  intro j
  rw [packedValue.2 j,inValue,outValue,ve.2]
  rfl
#print axioms value
end AspisR1.FIy_OccupancyPacked
end
