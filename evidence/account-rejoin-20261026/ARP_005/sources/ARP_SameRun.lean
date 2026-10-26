import ARP_SourceBoundary
import SCE_JointObserver
import F3S_Join
import Rc9_Top
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARP_SameRun
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_FixtureData

/-- Exact failed composition boundary. The SCE fixture's n1 accepts EVERY
account slice, whereas every installed source rejects the empty slice. Thus
neither F3S_Join nor Rc9 can use these SAME fixture natives with extraction.
This does not refute a future real-source fixture on the same retained bytes. -/
theorem fixture_not_extracted (ops : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    ¬ S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv := by
  intro extraction
  have same := extraction.stage1 id (⟨[],by simp⟩) (⟨[],by simp⟩)
  exact ARP_SourceBoundary.empty_accounts_reject ops id (⟨[],by simp⟩) saved same.symm

/-- Non-vacuity of the actual failure diagnosis: the approved game and
persistence, local native successes and retained real bytes coexist with the
IMPOSSIBILITY of the extraction bridge required by the proposed composition.
No full installed account acceptance or deployed headline is asserted. -/
theorem boundary_joint (ops : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (H : Bytes → State) :
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix
      n1 n2 copy allocator id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent observations)
      (CPG_Projection.ordinary observations (Hist_Nonvacuity.key 0#u8))
      (CPG_Projection.before observations) (CPG_Projection.tentative observations)
      (CPG_Projection.success observations) (CPG_Projection.loaded observations) ∧
    first n1 copy allocator e1 id data1 () = ok (.Ok (saved,SCE_FixtureWrappers.post1,())) ∧
    second n2 allocator e2 id data2 slot () = ok (.Ok (e2.heap,())) ∧
    (eval H (SCE_Experiment.submission (SCE_FixtureSubmission.adversary data1 data2 slot))).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    ¬ S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv :=
  ⟨SCE_FixtureGame.game,SCE_FixtureGame.persistence _,
    SCE_FixtureWrappers.first_success data1,SCE_FixtureWrappers.second_success data2 slot,
    SCE_FixtureSubmission.original_submission data1 data2 slot H,fixture_not_extracted ops hashv⟩

#print axioms fixture_not_extracted
#print axioms boundary_joint
#check @F3S_Join.accepted_log_eq
#check @Rc9_Top.deployed
#print axioms Rc9_Top.deployed
end AspisR1.ARP_SameRun
end
