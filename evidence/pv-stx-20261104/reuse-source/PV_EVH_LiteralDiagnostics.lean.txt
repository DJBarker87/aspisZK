import PV_EVH_Runtime
set_option autoImplicit false
namespace PV_EVH_LiteralDiagnostics
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes NativeEvent)

-- Exact request bytes from the adopted diagnostics.rs; no formatter carriers.
def errorBytes : Bytes := [99,108,105,101,110,116,32,101,114,114,111,114,10]
def panicBytes : Bytes := [99,108,105,101,110,116,32,112,97,110,105,99,10]

/-- write_all may return an io::Error that owns storage. Ignoring the Result
still runs its drop glue. It is not an infallible or effect-free writer law. -/
structure Writer where
  Error : Type
  writeAll : Bytes → Q (Except Error Unit)
  dropError : Error → Q Unit

def ignoreWrite (writer : Writer) (request : Bytes) : Q Unit := do
  let result ← writer.writeAll request
  match result with
  | .ok _ => pure ()
  | .error e => writer.dropError e

/-- Stored literal index stands for Error(&'static str), which owns no error
operand/backtrace. report ignores that literal and issues fixed request bytes. -/
def report (writer : Writer) (_literalIndex : Nat) : Q Unit := ignoreWrite writer errorBytes

def panicHook (writer : Writer) : Q Unit := ignoreWrite writer panicBytes

theorem report_operand_independent (writer : Writer) (a b : Nat) :
    report writer a = report writer b := rfl

theorem writer_error_runs_drop (writer : Writer) (request : Bytes) (w : State)
    (e : writer.Error) (h : (writer.writeAll request w).outcome = .returned (.ok (.error e))) :
    ignoreWrite writer request w =
      ⟨(writer.dropError e (writer.writeAll request w).state).outcome,
        (writer.dropError e (writer.writeAll request w).state).state,
        (writer.writeAll request w).events ++
          (writer.dropError e (writer.writeAll request w).state).events⟩ := by
  simp only [ignoreWrite,Bind.bind,PV_EVH_Runtime.bind,h]

theorem writer_abort_retains_prefix (writer : Writer) (request : Bytes) (w : State)
    (fault : Fault) (h : (writer.writeAll request w).outcome = .fault fault) :
    ignoreWrite writer request w =
      ⟨.fault fault,(writer.writeAll request w).state,(writer.writeAll request w).events⟩ :=
  bind_fault _ _ _ _ h

/-- This is request equality ONLY. It does not assert equal delivered bytes or
witness-independent writer state, timing, aborts, allocator state or errno. -/
theorem report_request (writer : Writer) (literalIndex : Nat) :
    report writer literalIndex = ignoreWrite writer errorBytes := rfl

#print axioms report_operand_independent
#print axioms writer_error_runs_drop
#print axioms writer_abort_retains_prefix
#print axioms report_request
end PV_EVH_LiteralDiagnostics
