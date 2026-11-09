import NOC_MerkleBounded
import NOM_MerkleGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOM_MerkleVerify
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalViews MultiproofConePhysicalTransport
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.NNY_MerkleShared (refDigest totalDigest total)
attribute [local instance] Classical.propDecidable

theorem reset (s : reference.Scratch) (zero : s.«at»=0#usize) : {s with «at»:=0#usize}=s := by
 cases s
 simp_all only

/-- Converse of NOC_MerkleBounded.endpoint: an accepted owned verifier at the
installed digest is the SAME accepted oracle-program endpoint. Uses only node
agreement (through NOC_MerkleBounded.height) and the verifier's own guards. -/
theorem endpoint (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NOC_MerkleBounded.NodeLeaf D H) (root : Array U8 32#usize) (physical : Slice U8)
 (s out : reference.Scratch) (zero : s.«at»=0#usize)
 (accepted : reference.verify_owned (refDigest D) () root s physical=.ok (true,out)) :
 (eval H (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out) := by
 obtain ⟨well,words,run,rootOK⟩ := NOM_MerkleGuard.guards (refDigest D) () root s out physical accepted
 have guard : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst) ∧
   physical.val.length%32=0 := ⟨well,words⟩
 obtain ⟨positive,bound,_⟩ := NNU_MerkleHead.source s guard.1
 have domain : MultiproofConeLevelIteration.Domain physical s := ⟨positive,bound,by rw [zero];simp⟩
 rw [reset s zero, NOC_MerkleBounded.height D H agree physical s domain] at run
 have same : (eval H
   (transport (MultiproofConePhysicalLevels.levels 18 s physical))).2=
   reference.levels (totalDigest D H) () s physical 18#u32 := by
   rw [transport_observation]
   exact NNU_MerkleLevels.eighteen_result _ () _ (total D H)
     (fun _ _ => rfl) s physical domain
 simp only [MultiproofConeVerifyState.verifyState,if_pos guard,eval_bind,eval,same,run,
   MultiproofConeVerifyState.finishState,rootOK]

/-- Converse of NOC_MerkleBounded.verify (installed P6 verify Ok ⇒ NKV verify Ok, SAME outputs). -/
theorem verify (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NOC_MerkleBounded.NodeLeaf D H) (root : Array U8 32#usize)
 (idx outIdx : Array U32 16#usize) (val outVal : Array (Array U8 32#usize) 16#usize)
 (n : Usize) (physical : Slice U8)
 (accepted : Port4B_VerifyInstall.verify (VTop_Checkpoint.digest D) ()
  .Two root idx val n physical=.ok (true,outIdx,outVal)) :
 NKV_ConcreteChildren.verify H
  (NKV_ConcreteChildren.digest H) () .Two root idx val n physical=
  .ok (true,outIdx,outVal) := by
 let s := NJV_EntryABI.initial idx val n
 unfold Port4B_VerifyInstall.verify at accepted
 change (do let (b,after) ← reference.verify_owned (refDigest D) () root s physical
            .ok (b,after.idx,after.val))=.ok (true,outIdx,outVal) at accepted
 cases hv : reference.verify_owned (refDigest D) () root s physical with
 | fail e => rw [hv] at accepted; simp only [bind_tc_fail] at accepted <;> cases accepted
 | div => rw [hv] at accepted; simp only [bind_tc_div] at accepted <;> cases accepted
 | ok pr =>
   rcases pr with ⟨b,after⟩
   rw [hv] at accepted
   simp only [bind_tc_ok,Result.ok.injEq,Prod.mk.injEq] at accepted
   obtain ⟨hb,hi,hval⟩ := accepted
   subst hb
   subst hi
   subst hval
   have e : (eval H (MultiproofConeVerifyState.verifyState root physical s)).2=(true,after) :=
     endpoint D H agree root physical s after rfl hv
   have e' : (eval H (NJV_TX2Returning.endpoint root physical idx val n)).2=(true,after) := e
   change Result.ok ((eval H (NJV_TX2Returning.endpoint root physical idx val n)).2.1,
     (eval H (NJV_TX2Returning.endpoint root physical idx val n)).2.2.idx,
     (eval H (NJV_TX2Returning.endpoint root physical idx val n)).2.2.val)=
     Result.ok (true,after.idx,after.val)
   exact congrArg (fun p : Bool × reference.Scratch =>
     (Result.ok (p.1,p.2.idx,p.2.val) : Result (Bool × Array U32 16#usize × Array (Array U8 32#usize) 16#usize))) e'

#print axioms reset
#print axioms endpoint
#print axioms verify
end AspisR1.NOM_MerkleVerify
end
