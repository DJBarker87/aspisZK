import Hir_NoFaultTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CallTotal
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_NoFault
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def oracle (store : Store) (call : Call A) : Program Bytes State (Effect A) :=
  match Hiq_ReleaseRoute.route call.data with
  | .first => bind (SdkC_Oracle.program (firstCode c hashv copy allocator id store call))
      (fun reply => .done (firstEffect store call reply))
  | .second => bind (SdkC_Oracle.program (secondCode c hashv allocator id store call))
      (fun reply => .done (store,.rollback,.inr reply))
  | .reject => .done (store,.rollback,.inr (.ok (.Err .InvalidInstructionData)))

def Safe (store : Store) (call : Call A) : Prop :=
  match Hiq_ReleaseRoute.route call.data with
  | .first => NoFault hashv (firstCode c hashv copy allocator id store call)
  | .second => NoFault hashv (secondCode c hashv allocator id store call)
  | .reject => True

theorem exact (store : Store) (call : Call A) (safe : Safe c hashv copy allocator id store call) :
    Hir_Call.oracle c hashv copy allocator id store call = oracle c hashv copy allocator id store call := by
  unfold Hir_Call.oracle oracle
  cases route : Hiq_ReleaseRoute.route call.data with
  | first =>
    dsimp only
    rw [Hir_NoFaultTransport.program_eq hashv _ (by simpa only [Safe,route] using safe)]
  | second =>
    dsimp only
    rw [Hir_NoFaultTransport.program_eq hashv _ (by simpa only [Safe,route] using safe)]
  | reject => rfl

#print axioms exact
end AspisR1.Hir_CallTotal
end
