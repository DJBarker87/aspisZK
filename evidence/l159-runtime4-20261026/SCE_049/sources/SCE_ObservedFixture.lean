import SCE_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ObservedFixture
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier SCE_FixtureData

/-- The shared observer returns the ACTUAL submitted JFx bytes in every H.
Its source acceptance flag is left as computed. This is not an assertion of
crypto acceptance by the local CPH native witnesses. -/
theorem returned {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (H : Bytes → State) :
    ∃ run : RunView,
      (eval H (runtime c hashv copy allocator id
        (SCE_FixtureSubmission.adversary data1 data2 slot))).2 = some run ∧
      run.2.1.stored = MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes ∧
      run.2.1.physical.bytes = MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes := by
  let a := SCE_FixtureSubmission.adversary data1 data2 slot
  let v := eval H (account c hashv copy allocator id a)
  let run : RunView := (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2))
  have observed : (eval H (runtime c hashv copy allocator id a)).2 = some run := by
    rw [runtime_eval]
  refine ⟨run,observed,?_,?_⟩
  · rw [SCE_Projection.stored c hashv copy allocator id a H run observed,
      SCE_FixtureSubmission.original_submission data1 data2 slot H]
  · rw [SCE_Projection.input_projection c hashv copy allocator id a H run observed,
      F3T_Canon.canon_eval,lift_eval,SCE_FixtureSubmission.original_submission data1 data2 slot H]
    rfl

#print axioms returned
end AspisR1.SCE_ObservedFixture
end
