import NMV_NoWriteSdk
set_option autoImplicit false
namespace NNH_NoWritePool
open RSL NMV_NoWrite

/-- RSL Revision 2: the owned getters are `RS.ofCloned` (clone allocation arm). -/
theorem ofCloned_free {A : Type} (r : Except ProgramError A) : Free (RS.ofCloned r) := by
 cases r with
 | ok a => exact pure_free _
 | error e =>
   show Free (if e.cloneAllocates then RS.bind (RS.lift Spec.alloc) (fun _ => RS.throw e)
     else RS.throw e)
   by_cases h : e.cloneAllocates = true
   · rw [if_pos h]
     exact rs_bind_free _ _ (lift_free _ alloc_free) (fun _ => pure_free _)
   · rw [if_neg h]
     exact pure_free _

theorem data_free (x : OwnedAccount) : Free x.data := ofCloned_free _

theorem dataLen_free (x : OwnedAccount) : Free x.data_len := ofCloned_free _

theorem verifierCheckpoint_free (x : OwnedAccount) (program : B32) (writable : Bool) :
 Free (verifierCheckpoint x program writable) := by
 unfold verifierCheckpoint
 split
 · exact pure_free _
 · exact rs_bind_free _ _ (dataLen_free x) (fun _ => check_free _ _)

syntax "free_steps" : tactic
macro_rules
 | `(tactic| free_steps) => `(tactic|
 first
 | exact pure_free _
 | exact alloc_free
 | exact panic_free
 | exact env_free _
 | exact ofExcept_free _
 | exact data_free _
 | exact dataLen_free _
 | exact ofCloned_free _
 | exact verifierCheckpoint_free _ _ _
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

#print axioms data_free
#print axioms dataLen_free
#print axioms ofCloned_free
#print axioms verifierCheckpoint_free
#print axioms pda_free
#print axioms master_free
#print axioms checkpoint_free
#print axioms lane_free
#print axioms registry_immutable_free
#print axioms registry_v1_free
#print axioms registry_free
end NNH_NoWritePool
