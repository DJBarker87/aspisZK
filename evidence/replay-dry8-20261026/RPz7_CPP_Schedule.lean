import RPz7_CPP_OracleSource
import RPz7_Hir_Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Schedule
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

inductive Schedule (A B : Type) where
  | done (value : B)
  | inspect (next : Store → Schedule A B)
  | ask (query : Bytes) (next : State → Schedule A B)
  | invoke (input : Invocation A) (next : Reply A → Schedule A B)
  | foreign (caller : S2W_ExtractionBoundary.Program) (key : Nat) (value : Cell)
      (next : S2X.AccountEvent → Schedule A B)
  | rollback (next : Schedule A B)

variable {A B F C : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def run (H : Bytes → State) (store : Store) : Schedule A B → Hir_Schedule.Output B
  | .done value => (store,[],value)
  | .inspect k => run H store (k store)
  | .ask query k => run H store (k (H query))
  | .invoke input k =>
    let head := CPP_Invocation.native n1 n2 copy allocator id store input
    let tail := run H head.1 (k head.2.2)
    (tail.1,head.2.1 :: tail.2.1,tail.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply n1 copy allocator id store (.foreign caller key value)
    let tail := run H head.1 (k head.2)
    (tail.1,head.2 :: tail.2.1,tail.2.2)
  | .rollback k =>
    let tail := run H store k
    (tail.1,.rollback :: tail.2.1,tail.2.2)

def erase : Schedule A B → Hir_Schedule.Schedule A B
  | .done value => .done value
  | .inspect k => .inspect (fun s => erase (k s))
  | .ask query k => .ask query (fun answer => erase (k answer))
  | .invoke input k =>
    if compatible input then .invoke input.call (fun reply => erase (k reply))
    else .rollback (erase (k (rejectedReply input)))
  | .foreign caller key value k => .foreign caller key value (fun event => erase (k event))
  | .rollback k => .rollback (erase k)

variable (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

def program (store : Store) : Schedule A B → Program Bytes State (Hir_Schedule.Output B)
  | .done value => .done (store,[],value)
  | .inspect k => program store (k store)
  | .ask query k => .ask query (fun answer => program store (k answer))
  | .invoke input k =>
    bind (CPP_Oracle.program c hashv copy allocator id store input) fun head =>
      bind (program head.1 (k head.2.2)) fun tail =>
        .done (tail.1,head.2.1 :: tail.2.1,tail.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply n1 copy allocator id store (.foreign caller key value)
    bind (program head.1 (k head.2)) fun tail =>
      .done (tail.1,head.2 :: tail.2.1,tail.2.2)
  | .rollback k =>
    bind (program store k) fun tail => .done (tail.1,.rollback :: tail.2.1,tail.2.2)
end AspisR1.CPP_Schedule
end
