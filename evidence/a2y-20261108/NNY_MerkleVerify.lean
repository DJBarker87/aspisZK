import NNY_MerkleEndpoint
import NKV_ConcreteChildren
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw

theorem verify (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H) (root : Array U8 32#usize)
 (idx outIdx : Array U32 16#usize) (val outVal : Array (Array U8 32#usize) 16#usize)
 (n : Usize) (physical : Slice U8)
 (accepted : NKV_ConcreteChildren.verify H
  (NKV_ConcreteChildren.digest H) () .Two root idx val n physical=
  .ok (true,outIdx,outVal)) :
 Port4B_VerifyInstall.verify (VTop_Checkpoint.digest D) ()
  .Two root idx val n physical=.ok (true,outIdx,outVal) := by
 let s := NJV_EntryABI.initial idx val n
 let out := (eval H (NJV_TX2Returning.endpoint root physical idx val n)).2
 change Result.ok (out.1,out.2.idx,out.2.val)=Result.ok (true,outIdx,outVal) at accepted
 have values := Result.ok.inj accepted
 have boolean : out.1=true := congrArg Prod.fst values
 have indices : out.2.idx=outIdx := congrArg (fun x => x.2.1) values
 have digests : out.2.val=outVal := congrArg (fun x => x.2.2) values
 have returned : (eval H
   (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out.2) :=
   Prod.ext boolean rfl
 have native := endpoint D H agree root physical s out.2 rfl returned
 unfold Port4B_VerifyInstall.verify
 change (do let (b,after) ← reference.verify_owned (refDigest D) () root s physical
            .ok (b,after.idx,after.val))=.ok (true,outIdx,outVal)
 rw [native]
 simp only [bind_tc_ok,indices,digests]
#print axioms verify
end AspisR1.NNY_MerkleShared
end
