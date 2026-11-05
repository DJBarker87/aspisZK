import NIN_ObserverFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIR_SameLawInstance
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
/-- Ruling (ao): recognition of the headline runtime; discharges no security obligation. -/
theorem realizes :
    NHZ_EXPERIMENT.Realizes (Tx := Tx) L copy allocator base err r n1 n2 hashv a
      (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator base err r n1 n2 hashv a) := by
  intro H
  rfl
/-- The admitted world's support criterion is the existing permitted_iff law,
not a new exporter or admission assumption. -/
theorem permitted_iff
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base r)) n1 n2 hashv)
    (H : Bytes → State) :
    ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator base err r n1 n2 hashv a
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err base r)
        hashv copy allocator CPH_Program.verifier a)) ↔
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator base err r n1 n2 hashv a H) :=
  ARX_AdmittedRuntime.permitted_iff L copy allocator base err r n1 n2 hashv a extraction H
#check AspisR1.NIN_Observer.canonical_from_initial
#check AspisR1.NIN_Observer.stored_public
#check AspisR1.NIN_Observer.outer_from_coverage
#check AspisR1.NIN_Observer.nested_from_outer
#check AspisR1.NIN_Observer.flag_from_results
#check AspisR1.NIN_Observer.accepted_iff
#print axioms realizes
#print axioms permitted_iff
end AspisR1.NIR_SameLawInstance
