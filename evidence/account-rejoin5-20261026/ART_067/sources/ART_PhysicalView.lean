import ART_FirstProjection
import ART_AccountAccepted
import ARQ_AccountView
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_PhysicalView
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

def physical (H : Bytes → State) : RawCutProverCompiler.RunView :=
  let v := eval H (ART_PartialAccount.account c hashv copy allocator id a)
  view (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2))

theorem accepted (H : Bytes → State)
    (yes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = true) :
    physical c hashv copy allocator id a H = ARQ_AccountView.physical c hashv copy allocator id a H := by
  unfold physical ARQ_AccountView.physical
  rw [ART_AccountAccepted.exact c hashv copy allocator id a H yes,SCE_Experiment.first_projection]

theorem replay (native H : Bytes → State)
    (consistent : ARS_AccountReplay.Consistent (ART_PartialAccount.account c hashv copy allocator id a) native H) :
    physical c hashv copy allocator id a H = physical c hashv copy allocator id a native := by
  unfold physical
  rw [ARS_AccountReplay.replay _ native H consistent]

#print axioms accepted
#print axioms replay
end AspisR1.ART_PhysicalView
end
