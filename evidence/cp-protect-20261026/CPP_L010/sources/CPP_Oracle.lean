import CPP_Classify
import Hir_CallSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Oracle
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def compatible {A : Type} (input : Invocation A) : Prop :=
  match Hiq_ReleaseRoute.route input.call.data with
  | .first => input.count = 3
  | .second => input.count = 7
  | .reject => True

def rejectedReply {A : Type} (input : Invocation A) : Reply A :=
  match Hiq_ReleaseRoute.route input.call.data with
  | .first => .inl (.ok (.Err .InvalidInstructionData))
  | .second | .reject => .inr (.ok (.Err .InvalidInstructionData))

def program {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A) :
    Program Bytes State (Effect A) :=
  if compatible input then Hir_Call.oracle c hashv copy allocator id store input.call
  else .done (store,.rollback,rejectedReply input)
end AspisR1.CPP_Oracle
end
