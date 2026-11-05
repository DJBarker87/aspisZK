import NHZ_SameLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHZ_EXPERIMENT
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment
attribute [local instance] Classical.propDecidable

/-- Field-by-field realization of the admitted physical observer. These are
explicit OPEN producer obligations. Full `Realizes` is a conclusion; no mass
inequality or conditioning factor is a premise. All fields refer to SAME a/H.
The `none` branch is the approved observer's outside-game zero extension,
not an assertion that native aborts never occur. -/
theorem realizes_from_fields {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (physical : F3T_Runtime.Runtime)
    (trace : ∀ H, (eval H physical).1 = (eval H (ART_PartialAccount.account
      (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).1)
    (admission : ∀ H, ((eval H physical).2).isSome = true ↔
      Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H))
    (events : ∀ H run, (eval H physical).2 = some run → run.1 =
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)).1)
    (carrier : ∀ H run, (eval H physical).2 = some run → run.2.1 =
      F3T_Canon.canonInput (F3T_ByteCarrier.input (FIp_Install.configuration err c r)
        (submitted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
          hashv copy allocator CPH_Program.verifier a)).2.1)))
    (failEvent : ∀ H run, (eval H physical).2 = some run → run.2.2 =
      accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)).2) :
    Realizes (Tx := Tx) L copy allocator c err r native1 native2 hashv a physical := by
  intro H
  rw [ARX_AdmittedRuntime.evaluation L copy allocator c err r native1 native2 hashv a extraction H]
  apply Prod.ext
  · exact trace H
  · dsimp only
    cases observed : (eval H physical).2 with
    | none =>
      have unsupported : ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
        intro yes
        have h := (admission H).mpr yes
        rw [observed] at h
        cases h
      rw [if_neg unsupported]
    | some run =>
      have supported : Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :=
        (admission H).mp (by rw [observed]; rfl)
      rw [if_pos supported,ART_Runtime.eval_runtime]
      congr 1
      exact Prod.ext (events H run observed) (Prod.ext (carrier H run observed) (failEvent H run observed))

#print axioms realizes_from_fields
end AspisR1.NHZ_EXPERIMENT
