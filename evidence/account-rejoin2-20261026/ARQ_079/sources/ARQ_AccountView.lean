import SCE_Experiment
import SCE_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_AccountView
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

/-- Literal physical view returned by the account observer, indexed to the
original first choice. The observer adds no queries and replays no verifier. -/
def physical {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State) : RawCutProverCompiler.RunView :=
  view ((eval H (account c hashv copy allocator id a)).1,
    (F3T_Canon.canonInput (input c (submitted (eval H a.first).2)),
      accepted (eval H (account c hashv copy allocator id a)).2))

theorem observed {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State) (run : RunView)
    (returned : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    view run = physical c hashv copy allocator id a H := by
  rw [runtime_eval,first_projection] at returned
  exact congrArg view (Option.some.inj returned).symm

#print axioms observed
end AspisR1.ARQ_AccountView
end
