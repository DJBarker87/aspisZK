import ARS_AccountReplay
import F3T_Probability
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_CylinderLaw
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open SCE_Experiment

/-- Any finite mixture supported on this execution's cylinder has exactly
its original observable law. The support restriction is explicit, so this
cannot silently replace the unconditioned ROM distribution. -/
theorem mean {A F C Coins : Type} [Fintype Coins] [Nonempty Coins]
    (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native : Bytes → State) (worlds : Coins → Bytes → State)
    (supported : ∀ coin, ARS_AccountReplay.Consistent
      (account c hashv copy allocator id a) native (worlds coin))
    (observe : List (Bytes × State) × GExq_AccountExperiment.Outcome A → Rat) :
    AspisV8R19.OracleResampling.mean
      (fun coin => observe (eval (worlds coin) (account c hashv copy allocator id a))) =
        observe (eval native (account c hashv copy allocator id a)) := by
  have same : (fun coin => observe (eval (worlds coin) (account c hashv copy allocator id a))) =
      (fun _ : Coins => observe (eval native (account c hashv copy allocator id a))) := by
    funext coin
    exact ARS_AccountReplay.law c hashv copy allocator id a native (worlds coin) (supported coin) observe
  rw [same,mean_const]

#print axioms mean
end AspisR1.ARS_CylinderLaw
end
