import SCE_AcceptedOutcome
import SCE_AccountBound
import SCE_AccountCollision
import SCE_AccountMass
import SCE_AccountReads
import SCE_AdaptivePadding
import SCE_Annotation
import SCE_ByteSuffix
import SCE_CarriedCut
import SCE_CompleteChronology
import SCE_CompleteSubmission
import SCE_ConditionalTop
import SCE_DeploymentProjection
import SCE_DivergencePrefix
import SCE_Execution
import SCE_Experiment
import SCE_FailurePrefix
import SCE_FailureZero
import SCE_FirstCutBytes
import SCE_FixtureAdmission
import SCE_FixtureBank
import SCE_FixtureBudget
import SCE_FixtureData
import SCE_FixtureGame
import SCE_FixtureRead
import SCE_FixtureReserve
import SCE_FixtureShape
import SCE_FixtureSubmission
import SCE_FixtureVersion
import SCE_FixtureWrappers
import SCE_GhostFrames
import SCE_InnerErrorPrefix
import SCE_InstalledSingleBound
import SCE_JointObserver
import SCE_ModelReadFrames
import SCE_NativeAccepted
import SCE_NativeFirst
import SCE_NativeSecond
import SCE_Nonvacuity
import SCE_Numeric
import SCE_ObservedFixture
import SCE_PaddingBudget
import SCE_PaddingCommonBudget
import SCE_PaddingConditions
import SCE_PaddingFirstPass
import SCE_PaddingNative
import SCE_PairAccepted
import SCE_Physical
import SCE_Projection
import SCE_PublicProjection
import SCE_Quantifiers
import SCE_RecoveredExtraction
import SCE_RejectedAccount
import SCE_ReplayExtractTransport
import SCE_ReplayExtractor
import SCE_ReplayFrames
import SCE_ReplayMaps
import SCE_ReplayTable
import SCE_ReplayWords
import SCE_RuntimeReturn
import SCE_SecondCutBytes
import SCE_SecondIndex
import SCE_SingleAnnotation
import SCE_SingleBound
import SCE_SingleExtract
import SCE_SingleKnown
import SCE_SingleNumerical
import SCE_SingleRuntime
import SCE_SingleTransport
import SCE_SnapshotRead
import SCE_SourceFirst
import SCE_SourceReadFrames
import SCE_SubmissionBound
import SCE_SubmissionExt
import SCE_SuffixShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_NoUniformPhysical
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier SCE_Experiment SCE_Execution SCE_AdaptivePadding

/-- The shared-adversary quantifier correction cannot by itself establish
uniform literal physical equality, even on one common finite query allowance.
This is conditional on an accepted source run, not an attack fixture. -/
theorem impossible {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (address : Bytes) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final)))
    (accepted : SCE_Experiment.accepted (eval H (account c hashv copy allocator id a)).2 = true)
    (rust : F3T_TwoPass.Verifier) (Q0 Q1 : Nat)
    (prefixBound : ∀ world, (eval world a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final world,
      (eval world (a.second i saved post final)).1.length ≤ Q1) :
    ¬ (∀ b : Adversary A,
      (∀ world, (eval world b.first).1.length ≤ Q0) →
      (∀ i saved post final world,
        (eval world (b.second i saved post final)).1.length ≤ Q1+1) →
      SCC_Physical.FirstPassBinding rust (F3T_Canon.canon (lift c (submission b)))
        (runtime c hashv copy allocator id b)) := by
  intro uniform
  have common := SCE_PaddingCommonBudget.both a address Q1 choiceBound
  apply SCE_PaddingFirstPass.not_both c hashv copy allocator id a address H saved post final first accepted rust
  exact ⟨uniform a prefixBound common.1, uniform (pad a address) prefixBound common.2⟩

#print axioms impossible
#print axioms AspisR1.Rc5_Top.deployed
#print axioms AspisR1.SCE_ConditionalTop.deployed
#print axioms AspisR1.SCE_Quantifiers.deployed_iff
#print axioms AspisR1.SCE_DeploymentProjection.stored
#print axioms AspisR1.SCE_Annotation.transport
#print axioms AspisR1.SCE_SingleExtract.extract
#print axioms AspisR1.SCE_InstalledSingleBound.source_bound
#print axioms AspisR1.SCE_JointObserver.joint
#print axioms AspisR1.SCE_FixtureBudget.zero
#print axioms AspisR1.SCE_PaddingNative.incompatible
#print axioms AspisR1.SCE_CompleteChronology.full_first_iff_empty_suffix
#print axioms AspisR1.SCE_Numeric.complete_start_not_headline
end AspisR1.SCE_NoUniformPhysical
end
