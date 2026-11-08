import NNU_MerkleEndpoint
import NKV_ConcreteChildren
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleVerify
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw

theorem selected (env : RSL.Env) (root : Array U8 32#usize)
 (idx outIdx : Array U32 16#usize) (val outVal : Array (Array U8 32#usize) 16#usize)
 (n : Usize) (physical : Slice U8)
 (accepted : NKV_ConcreteChildren.verify (LIBB_PartitionEnv.H env)
  (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) () .Two root idx val n physical=
  .ok (true,outIdx,outVal)) :
 Port4B_VerifyInstall.verify (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) ()
  .Two root idx val n physical=.ok (true,outIdx,outVal) := by
 let s := NJV_EntryABI.initial idx val n
 let out := (eval (LIBB_PartitionEnv.H env) (NJV_TX2Returning.endpoint root physical idx val n)).2
 change Result.ok (out.1,out.2.idx,out.2.val)=Result.ok (true,outIdx,outVal) at accepted
 have values := Result.ok.inj accepted
 have boolean : out.1=true := congrArg Prod.fst values
 have indices : out.2.idx=outIdx := congrArg (fun x => x.2.1) values
 have digests : out.2.val=outVal := congrArg (fun x => x.2.2) values
 have returned : (eval (LIBB_PartitionEnv.H env)
   (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out.2) :=
   Prod.ext boolean rfl
 have native := NNU_MerkleEndpoint.selected env root physical s out.2 rfl returned
 unfold Port4B_VerifyInstall.verify
 change (do let (b,after) ← reference.verify_owned (NNU_MerkleEnvironment.refDigest env) () root s physical
            .ok (b,after.idx,after.val))=.ok (true,outIdx,outVal)
 rw [native]
 simp only [bind_tc_ok,indices,digests]
theorem sdk (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (root : Array U8 32#usize) (idx outIdx : Array U32 16#usize)
 (val outVal : Array (Array U8 32#usize) 16#usize) (n : Usize) (physical : Slice U8)
 (accepted : NKV_ConcreteChildren.verify (LIBB_PartitionEnv.H env)
  (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) () .Two root idx val n physical=
  .ok (true,outIdx,outVal)) :
 Port4B_VerifyInstall.verify (VTop_Checkpoint.digest
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))) ()
  .Two root idx val n physical=.ok (true,outIdx,outVal) := by
 have same : AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
   (NNH_CorrectConfiguration.sdk m env err r)=LIBB_PartitionEnv.digest env := by rfl
 rw [same]
 exact selected env root idx outIdx val outVal n physical accepted
#print axioms selected
#print axioms sdk
end AspisR1.NNU_MerkleVerify
end
