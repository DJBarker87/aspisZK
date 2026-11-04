import PV_STX_Composition
import PV_RJ4IDB_NativeTrace
set_option autoImplicit false
namespace PV_STX_Diagnostics
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine
open PV_RJ4IDB (Bytes)
variable {Op : Type → Type 1}
-- Exact literals ported from evh LiteralDiagnostics (adopted diagnostics.rs).
def errorBytes : Bytes := [99,108,105,101,110,116,32,101,114,114,111,114,10]
def panicBytes : Bytes := [99,108,105,101,110,116,32,112,97,110,105,99,10]

def ignoreWrite {E : Type} (write : Bytes → Op (Except E Unit))
    (dropError : E → Op Unit) (request : Bytes) : Code Op Unit := do
  let result ← Code.call (write request)
  match result with
  | .ok _ => pure ()
  | .error e => Code.call (dropError e)

def report {E : Type} (write : Bytes → Op (Except E Unit))
    (dropError : E → Op Unit) (_literalIndex : Nat) : Code Op Unit :=
  ignoreWrite write dropError errorBytes

theorem report_operand_independent {E : Type} (write : Bytes → Op (Except E Unit))
    (dropError : E → Op Unit) (a b : Nat) : report write dropError a = report write dropError b := rfl

/-- Ignoring an io::Error does not erase its destructor or partial-writer
post-world. The actual syscall/guard interpreter is a separate construction. -/
theorem writer_error_drop {E W Ev : Type} (handler : Handler Op W Ev)
    (write : Bytes → Op (Except E Unit)) (dropError : E → Op Unit)
    (request : Bytes) (w : W) (e : E) (r : Result Unit)
    (hw : (handler (write request) w).answer = .returned (.ok (.error e)))
    (hd : (handler (dropError e) (handler (write request) w).world).answer = .returned r) :
    run handler 3 (ignoreWrite write dropError request) w =
      ⟨.returned r,(handler (dropError e) (handler (write request) w).world).world,
       (handler (write request) w).events ++
        (handler (dropError e) (handler (write request) w).world).events⟩ := by
  cases r <;> simp only [ignoreWrite,Bind.bind,Pure.pure,run,advance,start,step,
    resumed,continueWith,hw,hd,List.nil_append,List.append_nil]

#print axioms report_operand_independent
#print axioms writer_error_drop
end PV_STX_Diagnostics
