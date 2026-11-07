import NMV_NoWriteSdk
set_option autoImplicit false
namespace NMV_NoWritePool
open RSL NMV_NoWrite

syntax "free_steps" : tactic
macro_rules
 | `(tactic| free_steps) => `(tactic|
 first
 | exact pure_free _
 | exact alloc_free
 | exact panic_free
 | exact env_free _
 | exact ofExcept_free _
 | exact ofOption_free _ _
 | exact check_free _ _
 | exact index_free _ _
 | apply lift_free; free_steps
 | apply call_free; free_steps
 | apply rs_seq_free <;> free_steps
 | apply rs_bind_free
   · free_steps
   · intro _; free_steps
 | apply bind_free
   · free_steps
   · intro _; free_steps
 | apply emit_free; intro c b h; cases h
 | split <;> free_steps)

theorem pda_free (seeds : List Bytes) (p : B32) : Free (pdaOrErr seeds p) := by
 unfold pdaOrErr pdaCall
 free_steps

theorem master_free (L : PoolLib) (b : Bytes) : Free (decodeMasterBox L b) := by
 unfold decodeMasterBox
 free_steps

theorem checkpoint_free (L : PoolLib) (b : Bytes) : Free (decodeCheckpointBox L b) := by
 unfold decodeCheckpointBox
 free_steps

theorem lane_free (b : Bytes) : Free (TX2_217.Ref b) := by
 unfold TX2_217.Ref
 free_steps

theorem registry_immutable_free (L : PoolLib) (D : DeployedIds) (a : TX2_234.Args) :
 Free (TX2_234.immutableBranch L D a) := by
 unfold TX2_234.immutableBranch
 have hp := pda_free
 free_steps

theorem registry_v1_free (L : PoolLib) (D : DeployedIds) (a : TX2_234.Args) :
 Free (TX2_234.v1Branch L D a) := by
 unfold TX2_234.v1Branch
 free_steps

theorem registry_free (L : PoolLib) (D : DeployedIds) (a : TX2_234.Args) :
 Free (TX2_234.Ref L D a) := by
 unfold TX2_234.Ref
 free_steps

#print axioms pda_free
#print axioms master_free
#print axioms checkpoint_free
#print axioms lane_free
#print axioms registry_immutable_free
#print axioms registry_v1_free
#print axioms registry_free
end NMV_NoWritePool
