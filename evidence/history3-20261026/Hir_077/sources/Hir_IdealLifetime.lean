import Hir_TotalRecorded
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_IdealLifetime
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_LifetimeExperiment Hir_NoFault
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def program (initial : Store) (schedule : Schedule A (Call A)) : Program Bytes State (Execution A) :=
  bind (Hir_TotalRecorded.program c hashv native1 copy allocator id initial schedule) fun recorded =>
    bind (SdkC_Oracle.program (secondCode c hashv allocator id recorded.1.1 recorded.1.2.2)) fun reply =>
      .done (recorded,reply)

theorem program_eq
    (safe : ∀ store call, Hir_CallTotal.Safe c hashv copy allocator id store call)
    (secondSafe : ∀ store call, NoFault hashv (secondCode c hashv allocator id store call))
    (initial : Store) (schedule : Schedule A (Call A)) :
    Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule =
      program c hashv native1 copy allocator id initial schedule := by
  simp only [Hir_LifetimeExperiment.program,program,
    Hir_TotalRecorded.program_eq c hashv native1 copy allocator id safe initial schedule,
    Hir_NoFaultTransport.program_eq hashv _ (secondSafe _ _)]

theorem total_instance
    (total : ∀ parts, ∃ digest, hashv parts = .ok digest)
    (initial : Store) (schedule : Schedule A (Call A)) :
    Hir_LifetimeExperiment.program c hashv native1 copy allocator id initial schedule =
      program c hashv native1 copy allocator id initial schedule := by
  apply program_eq c hashv native1 copy allocator id ?_ ?_ initial schedule
  · intro store call
    unfold Hir_CallTotal.Safe
    cases Hiq_ReleaseRoute.route call.data with
    | first => exact Hir_NoFault.of_total hashv total _
    | second => exact Hir_NoFault.of_total hashv total _
    | reject => trivial
  · intro store call
    exact Hir_NoFault.of_total hashv total _

#print axioms program_eq
#print axioms total_instance
end AspisR1.Hir_IdealLifetime
end
