import NNY_MerkleHeight
import NNU_MerkleHead
import NNU_MerkleWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalViews MultiproofConePhysicalTransport
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem endpoint_total (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (root : Array U8 32#usize) (physical : Slice U8)
 (s out : reference.Scratch) (zero : s.«at»=0#usize)
 (accepted : (eval H
  (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out)) :
 reference.verify_owned (totalDigest D H) () root s physical=.ok (true,out) := by
 by_cases guard : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0
 · obtain ⟨positive,bound,indices⟩ := NNU_MerkleHead.source s guard.1
   have domain : MultiproofConeLevelIteration.Domain physical s := ⟨positive,bound,by rw [zero];simp⟩
   have reset : {s with «at»:=0#usize}=s := by cases s; simp_all only
   have same : (eval H
     (transport (MultiproofConePhysicalLevels.levels 18 s physical))).2=
     reference.levels (totalDigest D H) () s physical 18#u32 := by
     rw [transport_observation]
     exact NNU_MerkleLevels.eighteen_result _ () _ (total D H)
       (fun _ _ => rfl) s physical domain
   simp only [MultiproofConeVerifyState.verifyState,if_pos guard,eval_bind,eval,same] at accepted
   cases run : reference.levels (totalDigest D H) () s physical 18#u32 with
   | fail e => simp only [run,MultiproofConeVerifyState.finishState] at accepted;cases accepted
   | div => simp only [run,MultiproofConeVerifyState.finishState] at accepted;cases accepted
   | ok result =>
     cases result with
     | Stop stopped => simp only [run,MultiproofConeVerifyState.finishState] at accepted;cases accepted
     | Done final =>
       simp only [run,MultiproofConeVerifyState.finishState,Prod.mk.injEq] at accepted
       obtain ⟨rootOK,sameOut⟩ := accepted
       subst out
       apply NNU_MerkleWrapper.returned _ () root s final physical positive bound indices guard.2
       · rw [reset];exact run
       · exact rootOK
 · simp only [MultiproofConeVerifyState.verifyState,if_neg guard,eval] at accepted
   cases accepted
theorem endpoint (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NodeLeaf D H) (root : Array U8 32#usize) (physical : Slice U8)
 (s out : reference.Scratch) (zero : s.«at»=0#usize)
 (accepted : (eval H (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out)) :
 reference.verify_owned (refDigest D) () root s physical=.ok (true,out) := by
 have native := endpoint_total D H root physical s out zero accepted
 have guard : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0 := by
  by_contra bad
  simp only [MultiproofConeVerifyState.verifyState,if_neg bad,eval] at accepted
  cases accepted
 obtain ⟨positive,bound,indices⟩ := NNU_MerkleHead.source s guard.1
 have domain : MultiproofConeLevelIteration.Domain physical s := ⟨positive,bound,by rw [zero];simp⟩
 have reset : {s with «at»:=0#usize}=s := by cases s; simp_all only
 have success := Port4B_VerifyInstall.wrapper_success
  (fun s => reference.levels (totalDigest D H) () s physical 18#u32) root s out physical native
 apply NNU_MerkleWrapper.returned (refDigest D) () root s out physical positive bound indices guard.2
 · rw [reset,height D H agree physical s domain]
   rw [reset] at success
   exact success.1
 · exact success.2
#print axioms endpoint_total
#print axioms endpoint
end AspisR1.NNY_MerkleShared
end
