import NMX_R7_Port241
import NMX_R7_LiftMember
set_option autoImplicit false
noncomputable section
namespace NMX_R7_PortLaw241
open RSL RSL.TX2_241 NMX_R6_Observation NMX_R7_Port241
open NMS_R2Replay241

theorem public_member (validated : TX2_242.Validated L) (proofData checkpointData publicBytes : Bytes)
 (env : Env) :
 NMS_R2Replay241.afterPublic L V (NMS_R2Refine.observed NMX_R7_Verify241.verify)
  validated proofData checkpointData publicBytes env
  (NMX_R7_Port241.afterPublic validated proofData checkpointData publicBytes env) := by
 unfold NMS_R2Replay241.afterPublic NMX_R7_Port241.afterPublic
 split
 · rename_i reject
   rw [reject,RS.check_true,RS.seq_throw]
   rfl
 · rename_i accept
   have falseguard : (publicBytes.length != STATEMENT_BYTES) = false := by
    cases h : (publicBytes.length != STATEMENT_BYTES) <;> simp_all
   rw [falseguard,RS.check_false,RS.seq_pure]
   apply NMX_R7_LiftMember.member _ _ env _ _ rfl
   intro result
   exact rsmember _ _ env _ _ (NMX_R7_Port241.error_member result env) (fun _ => rfl)

theorem reads_member (validated : TX2_242.Validated L) (proofData checkpointData : Bytes) (env : Env) :
 NMS_R2Replay241.afterReads L V (NMS_R2Refine.observed NMX_R7_Verify241.verify)
  validated proofData checkpointData env (NMX_R7_Port241.afterReads validated proofData checkpointData env) := by
 unfold NMS_R2Replay241.afterReads NMX_R7_Port241.afterReads
 split
 · rename_i reject
   rw [reject,RS.check_true,RS.seq_throw]
   rfl
 · rename_i accept
   have falseguard : decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length) = false := by
    cases h : decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length) <;> simp_all
   rw [falseguard,RS.check_false,RS.seq_pure]
   split
   · rename_i reject
     rw [reject,RS.check_true,RS.seq_throw]
     rfl
   · rename_i accept
     have falseguard : (proofData.length != AFTERSTATE_BYTES + validated.proof_length) = false := by
      cases h : (proofData.length != AFTERSTATE_BYTES + validated.proof_length) <;> simp_all
     rw [falseguard,RS.check_false,RS.seq_pure]
     apply NMX_R7_LiftMember.member _ _ env _ _ (NMX_R7_Port241.encode_member _ env)
     intro enc
     apply rsmember _ _ env _ _ (NMX_R6_Port242.fromOption_member _ _ env)
     intro publicBytes
     exact public_member validated proofData checkpointData publicBytes env

theorem after_member (a : Args) (validated : TX2_242.Validated L) (env : Env) :
 NMS_R2Replay241.afterValidate L V (NMS_R2Refine.observed NMX_R7_Verify241.verify) a validated env
  (NMX_R7_Port241.afterValidate a validated env) := by
 unfold NMS_R2Replay241.afterValidate NMX_R7_Port241.afterValidate
 apply rsmember _ _ env _ _ (NMX_R7_Port241.index_member _ _ env)
 intro acc0
 apply rsmember _ _ env _ _ (NMX_R6_Clone.member _ env)
 intro proofData
 apply rsmember _ _ env _ _ (NMX_R7_Port241.index_member _ _ env)
 intro acc6
 apply rsmember _ _ env _ _ (NMX_R6_Clone.member _ env)
 intro checkpointData
 exact reads_member validated proofData checkpointData env

theorem replay_member (choices : NMX_R4_Authentication.Choices) (a : Args) (env : Env) :
 NMS_R2Replay241.replay L V (NMX_R6_Validation.validate choices) NMX_R7_Verify241.verify a env
  (NMX_R7_Port241.stage2 choices a env) := by
 unfold NMS_R2Replay241.replay NMX_R7_Port241.stage2
 split
 · rename_i reject
   rw [reject,RS.check_true,RS.seq_throw]
   rfl
 · rename_i accept
   have falseguard : (a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC) = false := by
    cases h : (a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC) <;> simp_all
   rw [falseguard,RS.check_false,RS.seq_pure]
   apply rsmember _ _ env _ _ rfl
   intro validated
   exact after_member a validated env

/-- Canonical port only: native source correspondence remains a separate
obligation and this theorem is not listed as the241 native candidate. -/
theorem canonical (choices : NMX_R4_Authentication.Choices) :
 RowSpec_241 L LIBB_PoolLib.deployed V (NMX_R7_Port241.stage2 choices) := by
 intro a env domain
 exact NMX_R7_Fold241.fold choices a domain env _ (replay_member choices a env)

#print axioms public_member
#print axioms reads_member
#print axioms after_member
#print axioms replay_member
#print axioms canonical
end NMX_R7_PortLaw241
end
