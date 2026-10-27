import PoolS2_PdaSeeds
import PoolS2_PdaPrimitives
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PdaMaster
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_PdaSeeds

theorem matched_exact (ops : Ops) (program key : Key) (master : Master) :
    pair_forest.master_address_matches ops program master key =
      registry.stored_bump_address_matches ops
        (masterCreate master.identity.asset_mint master.bump) program key := by
  simp [pair_forest.master_address_matches,masterSeed,masterPrefix,masterCreate,keyBytes,oneByte,lift]

theorem accepted (ops : Ops) (program key : Key) (master : Master)
    (h : pair_forest.master_address_matches ops program master key = ok true) :
    ops.create (masterCreate master.identity.asset_mint master.bump) program = ok (.Ok key) := by
  rw [matched_exact] at h
  exact PoolS2_PdaPrimitives.accepted ops _ program key h

theorem accepted_iff (ops : Ops) (program key : Key) (master : Master) :
    pair_forest.master_address_matches ops program master key = ok true ↔
      ops.create (masterCreate master.identity.asset_mint master.bump) program = ok (.Ok key) := by
  rw [matched_exact]
  exact ⟨PoolS2_PdaPrimitives.accepted ops _ program key,PoolS2_PdaPrimitives.ready ops _ program key⟩

theorem find_exact (ops : Ops) (program mint : Key) :
    pair_forest.pool_v1_pair_forest_master_address ops program mint =
      ops.find (masterFind mint) program := by
  simp [pair_forest.pool_v1_pair_forest_master_address,masterSeed,masterPrefix,asRef,
    masterFind,keyBytes,lift]

#print axioms matched_exact
#print axioms accepted
#print axioms accepted_iff
#print axioms find_exact
end AspisR1.PoolS2_PdaMaster
end
