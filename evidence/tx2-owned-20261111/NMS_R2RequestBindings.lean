import NMS_R2KeyEq
import NMS_R2N_RSLBindings
import NHJ_IdPacket
set_option autoImplicit false
noncomputable section
namespace NMS_R2RequestBindings
open Aeneas Aeneas.Std Result AdapterRw
open NMS_R2N_RSLScalars
attribute [local instance] Classical.propDecidable
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
/-- Full symbolic bit-pattern transport for the exact native key comparison. -/
theorem key (x y : Aeneas.Std.Array U8 32#usize) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 x y =
 ok (decide (b32 x ≠ b32 y)) := by
 rw [NMS_R2KeyEq.native,NMS_R2N_RSLScalarEq.key_neq]
 simp only [decide_not]

theorem profile (q : Request) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 q.verifier_profile r1_pool_adapter.PROFILE_BINDING =
 ok (decide (b32 q.verifier_profile ≠ RSL.PROFILE_BINDING)) := by
 rw [key,NMS_R2N_RSLBindings.profile]

theorem release (q : Request) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 q.verifier_release r1_pool_adapter.RELEASE_BINDING =
 ok (decide (b32 q.verifier_release ≠ RSL.RELEASE_BINDING)) := by
 rw [key,NMS_R2N_RSLBindings.release]

theorem pool (q : Request) (devnet : Bool) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 q.pool_program (NHJ_IdPacket.pool devnet) =
 ok (decide (b32 q.pool_program ≠ b32 (NHJ_IdPacket.pool devnet))) := key _ _
#print axioms key
#print axioms profile
#print axioms release
#print axioms pool
end NMS_R2RequestBindings
