import PV_EVH_LiteralWriteAll
set_option autoImplicit false
namespace PV_EVH_StderrWrite
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes NativeEvent)

/-- StderrRaw suppresses EBADF after the underlying write_all, dropping that
error while still inside the stderr/RefCell guards. This is not suppression of
its syscall prefix or of partial writes. -/
def handleBadFd {E : Type} (work : Q (Except E Unit))
    (dropError : E → Q Unit) (isBadFd : E → Bool) : Q (Except E Unit) := do
  let r ← work
  match r with
  | .ok _ => pure (.ok ())
  | .error e =>
    if isBadFd e then do
      let _ ← dropError e
      pure (.ok ())
    else pure (.error e)

/-- Ordinary Result exits release the RefCell/stderr guards before the caller
ignores (and destroys) the returned io::Error. Abort/fault prefixes are retained.
The guard and syscall implementations remain explicit native P obligations. -/
def scoped {E : Type} (acquire release : Q Unit) (work : Q (Except E Unit)) :
    Q (Except E Unit) := do
  let _ ← acquire
  let r ← work
  let _ ← release
  pure r

def writer (E : Type) (write : Bytes → Q (Except E Nat)) (dropError : E → Q Unit)
    (interrupted isBadFd : E → Bool) (writeZero : E) (oversize : Q (Except E Unit))
    (acquire release : Q Unit) (fuel : Nat) : PV_EVH_LiteralDiagnostics.Writer where
  Error := E
  writeAll := fun buf => scoped acquire release
    (handleBadFd (PV_EVH_LiteralWriteAll.run write dropError interrupted writeZero oversize fuel buf)
      dropError isBadFd)
  dropError := dropError

theorem badfd_drop {E : Type} (work : Q (Except E Unit))
    (dropError : E → Q Unit) (isBadFd : E → Bool) (w : State) (e : E)
    (hw : (work w).outcome = .returned (.ok (.error e))) (he : isBadFd e = true) :
    handleBadFd work dropError isBadFd w =
      let tail := (do let _ ← dropError e; pure (.ok ())) (work w).state
      ⟨tail.outcome,tail.state,(work w).events ++ tail.events⟩ := by
  simp only [handleBadFd,Bind.bind,PV_EVH_Runtime.bind,hw,he,if_true]

/-- Returned io::Error is released to the report caller only after guard
release. Its later destructor is LiteralDiagnostics.ignoreWrite's obligation. -/
theorem scoped_error {E : Type} (acquire release : Q Unit) (work : Q (Except E Unit))
    (w : State) (e : E)
    (ha : (acquire w).outcome = .returned (.ok ()))
    (hw : (work (acquire w).state).outcome = .returned (.ok (.error e))) :
    scoped acquire release work w =
      let tail := (do let _ ← release; pure (.error e)) (work (acquire w).state).state
      ⟨tail.outcome,tail.state,(acquire w).events ++
        ((work (acquire w).state).events ++ tail.events)⟩ := by
  simp only [scoped,Bind.bind,PV_EVH_Runtime.bind,ha,hw]

#print axioms badfd_drop
#print axioms scoped_error
end PV_EVH_StderrWrite
