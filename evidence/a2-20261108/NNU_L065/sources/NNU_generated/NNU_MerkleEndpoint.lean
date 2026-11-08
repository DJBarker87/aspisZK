import NNU_MerkleEnvironment
import NNU_MerkleHead
import NNU_MerkleWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleEndpoint
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalViews MultiproofConePhysicalTransport
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem selected (env : RSL.Env) (root : Array U8 32#usize) (physical : Slice U8)
 (s out : reference.Scratch) (zero : s.«at»=0#usize)
 (accepted : (eval (LIBB_PartitionEnv.H env)
  (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out)) :
 reference.verify_owned (NNU_MerkleEnvironment.refDigest env) () root s physical=.ok (true,out) := by
 by_cases guard : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0
 · obtain ⟨positive,bound,indices⟩ := NNU_MerkleHead.source s guard.1
   have domain : MultiproofConeLevelIteration.Domain physical s := ⟨positive,bound,by rw [zero];simp⟩
   have reset : {s with «at»:=0#usize}=s := by cases s; simp_all only
   have same : (eval (LIBB_PartitionEnv.H env)
     (transport (MultiproofConePhysicalLevels.levels 18 s physical))).2=
     reference.levels (NNU_MerkleEnvironment.refDigest env) () s physical 18#u32 := by
     rw [transport_observation]
     exact NNU_MerkleLevels.eighteen_result _ () _ (NNU_MerkleEnvironment.total env)
       (NNU_MerkleEnvironment.node env) s physical domain
   simp only [MultiproofConeVerifyState.verifyState,if_pos guard,eval_bind,eval,same] at accepted
   cases run : reference.levels (NNU_MerkleEnvironment.refDigest env) () s physical 18#u32 with
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
#print axioms selected
end AspisR1.NNU_MerkleEndpoint
end
