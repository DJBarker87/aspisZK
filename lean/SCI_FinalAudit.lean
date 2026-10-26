import SCI_Recovery
import SCG_Nonvacuity
import Rc7_Top
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCI_FinalAudit
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- The same SCE real-byte adversary has the actual retained submission and
loaded saved CP. This is an observer/bank fixture, not a claim of installed
cryptographic acceptance or joint inhabitance of all release hypotheses. -/
theorem real_byte_fixture (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (H : Bytes → State) :
    (eval H (SCE_Experiment.submission
      (SCE_FixtureSubmission.adversary data1 data2 slot))).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    MultiproofConeCanonical.bytesOf
      ((eval H ((SCE_FixtureSubmission.adversary data1 data2 slot).second
        (SCE_FixtureSubmission.firstInput data1) SCE_FixtureData.saved
        SCE_FixtureWrappers.post1 ())).2.entry.buffers
        ((eval H ((SCE_FixtureSubmission.adversary data1 data2 slot).second
          (SCE_FixtureSubmission.firstInput data1) SCE_FixtureData.saved
          SCE_FixtureWrappers.post1 ())).2.entry.handles 6).1).val =
      MultiproofConeCanonical.bytesOf SCE_FixtureData.saved.val := by
  refine ⟨SCE_FixtureSubmission.original_submission data1 data2 slot H,?_⟩
  change MultiproofConeCanonical.bytesOf (SCE_FixtureData.e2.buffers 2).val = _
  rw [SCE_FixtureRead.reader_checkpoint]

#print axioms real_byte_fixture
#print axioms AspisR1.SCI_SameWorld.assoc
#print axioms AspisR1.SCI_SameWorld.arbitrary_second
#print axioms AspisR1.SCI_SameWorld.game_does_not_select_second
#print axioms AspisR1.SCI_Projection.recorder_log
#print axioms AspisR1.SCI_Projection.final_audit
#print axioms AspisR1.SCI_Projection.selected_audit_obstruction
#print axioms AspisR1.SCI_Projection.prior_event
#print axioms AspisR1.SCI_Projection.different_audits
#print axioms AspisR1.SCI_Projection.OrderWitness.nonempty
#print axioms AspisR1.SCI_Projection.OrderWitness.child_none
#print axioms AspisR1.SCI_Projection.OrderWitness.empty_pred
#print axioms AspisR1.SCI_Projection.OrderWitness.address_pred
#print axioms AspisR1.SCI_Projection.OrderWitness.reordered_event
#print axioms AspisR1.SCI_Projection.OrderWitness.deleting_uncached
#print axioms AspisR1.SCI_Projection.OrderWitness.deleting_uncached_charged
#print axioms AspisR1.SCI_Recovery.ObserverBoundary.not_zero_query_conclusion
#print axioms AspisR1.SCI_Recovery.ObserverBoundary.extract_none
#print axioms AspisR1.SCI_Recovery.ObserverBoundary.failure_one
#print axioms AspisR1.SCI_Recovery.ObserverBoundary.unrestricted_runtime
#print axioms AspisR1.SCI_Recovery.ObserverBoundary.not_all_runtime_bounds
#print axioms AspisR1.SCI_Recovery.account_of_join
#print axioms AspisR1.SCI_Recovery.model_agreement
#print axioms AspisR1.SCI_Recovery.account_agreement
#print axioms AspisR1.SCI_Recovery.account_extract
#print axioms AspisR1.SCG_Nonvacuity.joint
#print axioms AspisR1.Rc7_Top.deployed

set_option pp.deepTerms true in
#print AspisR1.Rc7_Top.deployed
set_option pp.deepTerms true in
#print AspisR1.SCI_SameWorld.assoc
set_option pp.deepTerms true in
#print AspisR1.SCI_Recovery.account_agreement
end AspisR1.SCI_FinalAudit
end
