import NNU_MerkleLevels
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleEnvironment
open Aeneas Aeneas.Std Result MultiproofConeRef

def refDigest (env : RSL.Env) :=
 Port4B_VerifyInstall.digest (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env))

theorem total (env : RSL.Env) : MultiproofConeNodeDomain.HashTotal (refDigest env) () := by
 intro parts
 exact ⟨_,LIBB_PartitionEnv.digest_value env parts⟩

theorem node (env : RSL.Env) (left right : Array U8 32#usize) :
 (refDigest env).digest () (MultiproofConePhysicalDigest.parts left right)=
 .ok (MultiproofConePhysicalTransport.rawOracle (LIBB_PartitionEnv.H env)
  (MultiproofConePhysicalDigest.parts left right)) := NNU_MerkleDigest.node env left right

theorem sdk (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (parts : Slice (Slice U8)) :
 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r)).digest () parts=
 (LIBB_PartitionEnv.digest env).digest () parts := by
 rfl

theorem levels (env : RSL.Env) (height : Nat) (s : reference.Scratch) (physical : Slice U8)
 (domain : MultiproofConeLevelIteration.Domain physical s) :
 (AspisV8R19.MemoizedProgramLaw.eval (MultiproofConePhysicalTransport.rawOracle (LIBB_PartitionEnv.H env))
  (MultiproofConePhysicalLevels.levels height s physical)).2=
 MultiproofConeLevelIteration.iterate
  (fun s => reference.level_rows (refDigest env) () s physical 0#usize 0#usize) height s :=
 NNU_MerkleLevels.levels_result _ () _ (total env) (node env) height s physical domain
#print axioms total
#print axioms node
#print axioms sdk
#print axioms levels
end AspisR1.NNU_MerkleEnvironment
end
