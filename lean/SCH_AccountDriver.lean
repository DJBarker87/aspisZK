import SCH_AccountDecoded
import SCH_DriverAcceptance
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_AccountDriver
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open MultiproofConeCanonical

/-- Same-adversary reverse route at EACH H. Byte association remains in the
output continuation, not smuggled into a new unconditional security theorem. -/
theorem accepted {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) :
    let r := Rc5_Install.configuration err c reservation
    ∀ H : Bytes → State,
    SCE_Experiment.accepted (eval H (account r hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      SourceCuts (SCH_IdealSdk.dictionary r hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes) saved f s ∧
      (bytesOf s.proof.val = bytesOf f.proof.val →
       bytesOf s.pub.val = bytesOf f.pub.val →
       bytesOf s.checkpoint.val = bytesOf saved.val →
       (eval H (F3T_Installed.source r hashv (F3T_ByteCarrier.input r (eval H (submission a)).2))).2 = true) := by
  dsimp only
  intro H success
  obtain ⟨saved,post,final,f,s,cuts,decoded,submitted⟩ :=
    SCH_AccountDecoded.accepted c err reservation hashv copy allocator id a H success
  refine ⟨saved,post,final,f,s,cuts,?_⟩
  intro proof pub checkpoint
  rw [submitted]
  exact SCH_DriverAcceptance.accepted c err reservation hashv H _ _ saved f s cuts decoded proof pub checkpoint

#print axioms accepted
end AspisR1.SCH_AccountDriver
end
