import NIN_ObserverPredicates
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_Observer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
section
variable {A C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
local notation "cfg" => FIp_Install.configuration err base r

/-- The producer exports the actual native wrapper Results. Retained extraction
then identifies the literal flag for every Result arm, including fail/div/Err.
The parent-to-exporter association is explicit and remains OPEN. -/
theorem flag_from_results
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
        cfg.query cfg.geometry cfg.boundaries cfg.std) n1 n2 hashv)
    (physical : F3T_Runtime.Runtime) (native : Bytes → State)
    (coverage : ∀ H, ART_PartialAccount.Certificate cfg hashv copy allocator
      CPH_Program.verifier a native H)
    (exported : ∀ H run, (eval H physical).2 = some run → run.2.2 =
      accepted (ARS_NativeOutcome.wrappers copy allocator CPH_Program.verifier a n1 n2 native)) :
    LiteralFlag copy allocator base err r hashv a physical := by
  intro H run observed
  rw [ART_Outcome.native cfg hashv copy allocator CPH_Program.verifier a native H
    (coverage H) n1 n2 extraction]
  exact exported H run observed

/-- The literal accepted flag exposes BOTH success Results; there is no
boolean substitute for a native Ok observation and no removal of rejections. -/
theorem accepted_iff {A : Type} (out : GExq_AccountExperiment.Outcome A) :
    accepted out = true ↔
    (∃ first, out.2.1 = ok (.Ok first)) ∧
    (∃ second reply, out.2.2 = some (second,ok (.Ok reply))) := by
  rcases out with ⟨i,f,s⟩
  cases f with
  | fail error => simp [accepted]
  | div => simp [accepted]
  | ok f =>
    cases f with
    | Err error => simp [accepted]
    | Ok value =>
      cases s with
      | none => simp [accepted]
      | some s =>
        rcases s with ⟨j,reply⟩
        cases reply with
        | fail error => simp [accepted]
        | div => simp [accepted]
        | ok reply => cases reply <;> simp [accepted]
#print axioms flag_from_results
#print axioms accepted_iff
end
end AspisR1.NIN_Observer
