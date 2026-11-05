import NIN_ObserverCanonical
import NIN_ObserverTrace
import NIN_ObserverResults
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_Observer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Instantiate NHZ item 5 without replacing any of its five physical producer
obligations by a freely selected run. This theorem ORGANIZES these hypotheses;
it does not discharge admission or native exporter existence. The preceding
modules reduce items 1/3/4/5 to their exact lower-level producer associations. -/
theorem realizes {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base r)) n1 n2 hashv)
    (physical : F3T_Runtime.Runtime)
    (outer : OuterTrace copy allocator base err r hashv a physical)
    (admission : AdmittedSupport (Tx := Tx) L copy allocator base err r n1 n2 hashv a physical)
    (nested : NestedEvents copy allocator base err r hashv a physical)
    (canonical : CanonicalInput copy allocator base err r hashv a physical)
    (flag : LiteralFlag copy allocator base err r hashv a physical) :
    NHZ_EXPERIMENT.Realizes (Tx := Tx) L copy allocator base err r n1 n2 hashv a physical :=
  NHZ_EXPERIMENT.realizes_from_fields L copy allocator base err r n1 n2 hashv a
    extraction physical outer admission nested canonical flag
#print axioms realizes
end AspisR1.NIN_Observer
