import RPz7_Hir_ProvenanceModel
import RPz7_CPP_ProgramErasure
import RPz7_Hir_ScheduleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Atomic
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Reply (B : Type) := Result (core.result.Result B AdapterRw.solana_program_error.ProgramError)
abbrev Output (B : Type) := Hir_Schedule.Output (Reply B)

def settle {B : Type} (before : Store) (tentative : Output B) : Output B :=
  match tentative.2.2 with
  | .ok (.Ok _) => tentative
  | _ => (before,[.rollback],tentative.2.2)

def committed {B : Type} (reply : Reply B) : Prop := ∃ b, reply = .ok (.Ok b)

variable {A B F C : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def run (H : Bytes → State) (before : Store) (code : CPP_Schedule.Schedule A (Reply B)) : Output B :=
  settle before (CPP_Schedule.run n1 n2 copy allocator id H before code)

def sites (H : Bytes → State) (before : Store) (code : CPP_Schedule.Schedule A (Reply B)) : List (Hir_ProvenanceModel.CallAt A) :=
  match (CPP_Schedule.run n1 n2 copy allocator id H before code).2.2 with
  | .ok (.Ok _) => Hir_ProvenanceModel.calls n1 n2 copy allocator id H before (erase code)
  | _ => []

variable (c : DrvC_Installation.Configuration F C) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def program (before : Store) (code : CPP_Schedule.Schedule A (Reply B)) : Program Bytes State (Output B) :=
  AspisV8R19.OracleProgramOps.bind (CPP_Schedule.program n1 copy allocator id c hashv before code)
    (fun tentative => .done (settle before tentative))
end AspisR1.CPP_Atomic
end
