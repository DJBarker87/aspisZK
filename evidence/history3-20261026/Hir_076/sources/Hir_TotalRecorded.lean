import Hir_CallTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_TotalRecorded
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- In-memory observations of the reached calls. Recording asks no oracle
question and does not select an independent native execution. -/
def program (store : Store) : Schedule A B → Program Bytes State (Output B × List (CallAt A))
  | .done value => .done ((store,[],value),[])
  | .inspect k => program store (k store)
  | .ask query k => .ask query (fun answer => program store (k answer))
  | .invoke call k =>
    bind (Hir_CallTotal.oracle c hashv copy allocator id store call) fun head =>
      bind (program head.1 (k head.2.2)) fun tail =>
        .done ((tail.1.1,head.2.1 :: tail.1.2.1,tail.1.2.2),⟨store,call⟩ :: tail.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)
    bind (program head.1 (k head.2)) fun tail =>
      .done ((tail.1.1,head.2 :: tail.1.2.1,tail.1.2.2),tail.2)
  | .rollback k =>
    bind (program store k) fun tail => .done ((tail.1.1,.rollback :: tail.1.2.1,tail.1.2.2),tail.2)

/-- Exact all-world transport to the ordinary ideal-oracle source syntax.
The missing native syscall-totality instance is NOT inferred from P1. -/
theorem program_eq
    (safe : ∀ store call, Hir_CallTotal.Safe c hashv copy allocator id store call)
    (store : Store) (schedule : Schedule A B) :
    Hir_Recorded.program c hashv native1 copy allocator id store schedule =
      program c hashv native1 copy allocator id store schedule := by
  induction schedule generalizing store with
  | done value => rfl
  | inspect k ih => exact ih store store
  | ask query k ih =>
    simp only [Hir_Recorded.program,program,ih]
  | invoke call k ih =>
    simp only [Hir_Recorded.program,program,Hir_CallTotal.exact c hashv copy allocator id store call (safe store call),ih]
  | foreign caller key value k ih =>
    simp only [Hir_Recorded.program,program,ih]
  | rollback k ih =>
    simp only [Hir_Recorded.program,program,ih]

#print axioms program_eq

end AspisR1.Hir_TotalRecorded
end
