import R1Z.PV_RunJoin_InverseChain20
import R1Z.PV_RunJoin_OutputPair17
import R1Z.PV_RunJoin_OccupiedValidation16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OutputConstructor20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
abbrev first := PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment
abbrev second := PV_RunJoin_RecordedTransfer.publicRecord.change_commitment

def pair : pair_tree_profile.PoolV1PairLeafWitnessV1 := ⟨first,1#u32,second,225401153#u32⟩

theorem first_canonical : Canon8 first := by intro i hi;interval_cases i <;> decide
#print axioms first_canonical
theorem second_canonical : Canon8 second := by intro i hi;interval_cases i <;> decide
#print axioms second_canonical

theorem validate : pair_tree_profile.PoolV1PairLeafWitnessV1.validate pair = ok (.Ok ()) := by
  apply PV_RunJoin_OccupiedValidation16.validates
  · exact first_canonical
  · exact second_canonical
  · decide
  · decide
  · with_unfolding_all exact PV_RunJoin_InverseChain20.product
#print axioms validate

theorem source : pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs first second = ok (.Ok pair) := by
  rw [pair_tree_profile.PoolV1PairLeafWitnessV1.two_outputs]
  rw [PV_RunJoin_DigestCanonical16.tree_true first first_canonical]
  simp only [bind_tc_ok,↓reduceIte]
  rw [PV_RunJoin_DigestCanonical16.tree_true second second_canonical]
  simp only [bind_tc_ok,↓reduceIte]
  rw [pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE]
  have hi : Array.index_usize second 7#usize = ok 351017421#u32 := by with_unfolding_all rfl
  rw [hi]
  simp only [bind_tc_ok]
  have hz : aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq 351017421#u32 aspis_core.field.M31.ZERO = ok false := by with_unfolding_all rfl
  rw [hz]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_InverseChain20.inverse]
  simp only [bind_tc_ok]
  have hv : pair_tree_profile.PoolV1PairLeafWitnessV1.validate
      ⟨first,aspis_core.field.M31.ONE,second,225401153#u32⟩ = ok (.Ok ()) := by
    with_unfolding_all exact validate
  rw [hv]
  with_unfolding_all rfl
#print axioms source
end R1Z.PV_RunJoin_OutputConstructor20
