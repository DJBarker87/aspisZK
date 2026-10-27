import RPz7_Hir_CallClassify
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Schedule
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers GExq_AccountExperiment Hir_Call
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A finite adaptive native schedule. Chosen before H; later calls may depend
on every prior reply, read, account observation and rollback. No event list or
final loaded entry is supplied by a caller. -/
inductive Schedule (A B : Type) where
  | done (value : B)
  | inspect (next : Store → Schedule A B)
  | ask (query : Bytes) (next : State → Schedule A B)
  | invoke (call : Call A) (next : Reply A → Schedule A B)
  | foreign (caller : S2W_ExtractionBoundary.Program) (key : Nat) (value : Cell)
      (next : S2X.AccountEvent → Schedule A B)
  | rollback (next : Schedule A B)

abbrev Output (B : Type) := Store × List S2X.AccountEvent × B

variable {A B F C : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def run (H : Bytes → State) (store : Store) : Schedule A B → Output B
  | .done value => (store,[],value)
  | .inspect k => run H store (k store)
  | .ask query k => run H store (k (H query))
  | .invoke call k =>
    let head := Hir_Call.native native1 native2 copy allocator id store call
    let tail := run H head.1 (k head.2.2)
    (tail.1,head.2.1 :: tail.2.1,tail.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)
    let tail := run H head.1 (k head.2)
    (tail.1,head.2 :: tail.2.1,tail.2.2)
  | .rollback k =>
    let tail := run H store k
    (tail.1,.rollback :: tail.2.1,tail.2.2)

variable (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def program (store : Store) : Schedule A B → Program Bytes State (Output B)
  | .done value => .done (store,[],value)
  | .inspect k => program store (k store)
  | .ask query k => .ask query (fun answer => program store (k answer))
  | .invoke call k =>
    bind (Hir_Call.oracle c hashv copy allocator id store call) fun head =>
      bind (program head.1 (k head.2.2)) fun tail =>
        .done (tail.1,head.2.1 :: tail.2.1,tail.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)
    bind (program head.1 (k head.2)) fun tail =>
      .done (tail.1,head.2 :: tail.2.1,tail.2.2)
  | .rollback k =>
    bind (program store k) fun tail => .done (tail.1,.rollback :: tail.2.1,tail.2.2)

end AspisR1.Hir_Schedule
end
