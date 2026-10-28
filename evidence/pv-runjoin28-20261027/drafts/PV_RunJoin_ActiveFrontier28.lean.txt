import R1Z.BuilderForestAdmissionPort
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ActiveFrontier28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

/-- At index one, the actual extracted tree frontier-validation loop skips
slot zero completely. This is a single symbolic loop step, not an evaluation
of a hash or a whole preparation. -/
theorem active_slot_skipped
    (frontier : Array (Array U32 8#usize) 20#usize)
    (empty : Array (Array U32 8#usize) 21#usize) :
    incremental_merkle.tree_reference.validate_owned_loop
      1#u64 frontier empty (.Ok ()) 0#usize =
    incremental_merkle.tree_reference.validate_owned_loop
      1#u64 frontier empty (.Ok ()) 1#usize := by
  conv_lhs => rw [incremental_merkle.tree_reference.validate_owned_loop]
  rfl
#print axioms active_slot_skipped
end R1Z.PV_RunJoin_ActiveFrontier28
