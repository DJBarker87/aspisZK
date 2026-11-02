import PV_EVH_LiteralWriteAll
set_option autoImplicit false
namespace PV_EVH_StderrWrite
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes NativeEvent)

/-- StderrRaw suppresses EBADF after the underlying write_all, dropping that
error while still inside the stderr/RefCell guards. This is not suppression of
its syscall prefix or of partial writes. -/
def handleBadFd {E : Type} (work : Q (Except E Unit))
    (dropError : E → Q Unit) (isBadFd : E → Q Bool) : Q (Except E Unit) := do
  let r ← work
  match r with
  | .ok _ => pure (Except.ok () : Except E Unit)
  | .error e =>
    let bad ← isBadFd e
    if bad then do
      let _ ← dropError e
      pure (Except.ok () : Except E Unit)
    else pure (Except.error e : Except E Unit)

/-- Ordinary Result exits release the RefCell/stderr guards before the caller
ignores (and destroys) the returned io::Error. Abort/fault prefixes are retained.
The guard and syscall implementations remain explicit native P obligations. -/
def withGuards {E : Type} (acquire release : Q Unit) (work : Q (Except E Unit)) :
    Q (Except E Unit) := do
  let _ ← acquire
  let r ← work
  let _ ← release
  pure r

def writer (driver : PV_EVH_WriteAll.Driver) (dropError : driver.Error → Q Unit)
    (isBadFd : driver.Error → Q Bool) (acquire release : Q Unit) (fuel : Nat) :
    PV_EVH_LiteralDiagnostics.Writer where
  Error := driver.Error
  writeAll := fun buf => withGuards acquire release
    (handleBadFd (PV_EVH_WriteAll.loop driver fuel buf) dropError isBadFd)
  dropError := dropError

theorem badfd_dispatch {E : Type} (work : Q (Except E Unit))
    (dropError : E → Q Unit) (isBadFd : E → Q Bool) (w : State) (e : E)
    (hw : (work w).outcome = .returned (.ok (.error e))) :
    handleBadFd work dropError isBadFd w =
      let tail : PV_EVH_Runtime.Run (Except E Unit) := (do
        let bad ← isBadFd e
        if bad then do let _ ← dropError e; pure (Except.ok () : Except E Unit)
        else pure (Except.error e : Except E Unit)) (work w).state
      ⟨tail.outcome,tail.state,(work w).events ++ tail.events⟩ := by
  simp only [handleBadFd,Bind.bind,PV_EVH_Runtime.bind,hw]

/-- Returned io::Error is released to the report caller only after guard
release. Its later destructor is LiteralDiagnostics.ignoreWrite's obligation. -/
theorem scoped_error {E : Type} (acquire release : Q Unit) (work : Q (Except E Unit))
    (w : State) (e : E)
    (ha : (acquire w).outcome = .returned (.ok ()))
    (hw : (work (acquire w).state).outcome = .returned (.ok (.error e))) :
    withGuards acquire release work w =
      let tail : PV_EVH_Runtime.Run (Except E Unit) := (do let _ ← release; pure (Except.error e : Except E Unit)) (work (acquire w).state).state
      ⟨tail.outcome,tail.state,(acquire w).events ++
        ((work (acquire w).state).events ++ tail.events)⟩ := by
  simp only [withGuards,Bind.bind,PV_EVH_Runtime.bind,ha,hw]

#print axioms badfd_dispatch
#print axioms scoped_error
end PV_EVH_StderrWrite
