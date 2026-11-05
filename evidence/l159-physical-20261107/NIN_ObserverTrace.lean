import NIN_ObserverPredicates
import NIC_DriverPackets
import NIF_FieldsEffect
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

/-- Exact attempted-log transport through partial source coverage. The physical
export and both chronological caller packets remain producer obligations.
No syscall totality, sorting, deduplication or successful-only log is used. -/
theorem outer_from_coverage (physical : F3T_Runtime.Runtime) (native : (Bytes → State) → Bytes → State)
    (coverage : ∀ H, ART_PartialAccount.Certificate cfg hashv copy allocator
      CPH_Program.verifier a (native H) H)
    (exported : ∀ H, (eval H physical).1 = (ART_PartialAccount.represented cfg hashv
      copy allocator CPH_Program.verifier a (native H) H).1) :
    OuterTrace copy allocator base err r hashv a physical := by
  intro H
  exact (exported H).trans (congrArg Prod.fst
    (ART_Coverage.execution cfg hashv copy allocator CPH_Program.verifier a (native H) H (coverage H))).symm

/-- If the nested exporter records the outer occurrence log, only item 1 is
needed to establish item 3. Proving this exporter association remains OPEN. -/
theorem nested_from_outer (physical : F3T_Runtime.Runtime)
    (outer : OuterTrace copy allocator base err r hashv a physical)
    (exported : ∀ H run, (eval H physical).2 = some run → run.1 = (eval H physical).1) :
    NestedEvents copy allocator base err r hashv a physical := by
  intro H run observed
  exact (exported H run observed).trans (outer H)
#print axioms outer_from_coverage
#print axioms nested_from_outer
end
end AspisR1.NIN_Observer
