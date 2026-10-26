import SCE_PublicProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_RuntimeReturn
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

/-- Symbolic returned-view construction. Large native carriers are left as
abstract arguments throughout kernel checking. -/
theorem returned {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State) :
    ∃ run : RunView, (eval H (runtime c hashv copy allocator id a)).2 = some run ∧
      run.2.1.stored = (eval H (submission a)).2.stored ∧
      run.2.1.physical.bytes = (eval H (submission a)).2.publicBytes := by
  let v := eval H (account c hashv copy allocator id a)
  let run : RunView := (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2))
  have observed : (eval H (runtime c hashv copy allocator id a)).2 = some run := by
    rw [runtime_eval]
  exact ⟨run,observed,SCE_Projection.stored c hashv copy allocator id a H run observed,
    SCE_PublicProjection.bytes c hashv copy allocator id a H run observed⟩
#print axioms returned
end AspisR1.SCE_RuntimeReturn
end
