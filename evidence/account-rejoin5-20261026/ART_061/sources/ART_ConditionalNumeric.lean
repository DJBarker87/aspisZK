import ART_RuntimeDomination
import ARS_ReachedNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_ConditionalNumeric
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

/-- Composition consumer only: the unproved all-world clean law remains
explicit. Failed syscalls add ZERO loss; this is not a replacement deployed top. -/
theorem numeric {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ARS_ReachedBudget.ChoiceBound c hashv copy allocator id a Q1)
    (law : SCF_RequiredTransport.CleanAccountTransport c D hashv copy allocator id a Q0 Q1
      ARQ_Observer.project (ARQ_Observer.select c id)) :
    F3T_RuntimeBound.failureModel (ART_Runtime.runtime c hashv copy allocator id a) ≤
      F3T_Numeric.total (Q0+Q1) := by
  have upper := ARS_ReachedNumeric.numeric c D hashv copy allocator id a Q0 Q1 prefixBound choiceBound law
  have domination := ART_RuntimeDomination.averaged c hashv copy allocator id a
  unfold F3T_RuntimeBound.failureModel at *
  linarith

#print axioms numeric
end AspisR1.ART_ConditionalNumeric
end
