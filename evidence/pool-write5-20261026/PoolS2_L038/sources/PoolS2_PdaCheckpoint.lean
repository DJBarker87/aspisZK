import PoolS2_PdaSeeds
set_option autoImplicit false
namespace AspisR1.PoolS2_PdaCheckpoint
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_PdaSeeds

theorem exact (ops : Ops) (program master : Key) (seq : U64) :
    pair_forest.pool_v1_pair_forest_checkpoint_address ops program master seq =
      ops.find (checkpointFind master seq) program := by
  simp [pair_forest.pool_v1_pair_forest_checkpoint_address,checkpointSeed,checkpointPrefix,
    checkpointFind,asRef,keyBytes,sequenceBytes,lift]

theorem returned (ops : Ops) (program master key : Key) (seq : U64) (bump : U8)
    (h : pair_forest.pool_v1_pair_forest_checkpoint_address ops program master seq = ok (key,bump)) :
    ops.find (checkpointFind master seq) program = ok (key,bump) := by
  simpa only [exact] using h

#print axioms exact
#print axioms returned
end AspisR1.PoolS2_PdaCheckpoint
