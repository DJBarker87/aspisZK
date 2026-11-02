import PV_EVH_LiteralDiagnostics
set_option autoImplicit false
namespace PV_EVH_WriteAll
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_RJ4IDB (Bytes)

/-- All reached operations remain explicit, including ErrorKind inspection,
WriteZero construction, interrupted-error destruction and bad-count panic. -/
structure Driver where
  Error : Type
  write : Bytes → Q (Except Error Nat)
  interrupted : Error → Q Bool
  dropInterrupted : Error → Q Unit
  writeZero : Q Error
  badCount : Nat → Bytes → Q (Except Error Unit)

def loop (driver : Driver) : Nat → Bytes → Q (Except driver.Error Unit)
  | _, [] => PV_EVH_Runtime.lift (.ok (.ok ()))
  | 0, _ :: _ => fun w => ⟨.exhausted,w,[]⟩
  | fuel+1, pending@(_ :: _) => do
    let result ← driver.write pending
    match result with
    | .ok 0 => do
      let e ← driver.writeZero
      pure (.error e)
    | .ok (n+1) =>
      if n+1 ≤ pending.length then loop driver fuel (pending.drop (n+1))
      else driver.badCount (n+1) pending
    | .error e => do
      let retry ← driver.interrupted e
      if retry then do
        let _ ← driver.dropInterrupted e
        loop driver fuel pending
      else pure (.error e)

def writer (driver : Driver) (fuel : Nat) (dropError : driver.Error → Q Unit) :
    PV_EVH_LiteralDiagnostics.Writer :=
  ⟨driver.Error,loop driver fuel,dropError⟩

theorem empty_request (driver : Driver) (fuel : Nat) (w : State) :
    loop driver fuel [] w = ⟨.returned (.ok (.ok ())),w,[]⟩ := by
  cases fuel <;> rfl

theorem exhausted_pending (driver : Driver) (head : UInt8) (tail : Bytes) (w : State) :
    loop driver 0 (head :: tail) w = ⟨.exhausted,w,[]⟩ := rfl

theorem raw_write_fault (driver : Driver) (fuel : Nat) (head : UInt8) (tail : Bytes)
    (w : State) (fault : Fault)
    (h : (driver.write (head :: tail) w).outcome = .fault fault) :
    loop driver (fuel+1) (head :: tail) w =
      ⟨.fault fault,(driver.write (head :: tail) w).state,
        (driver.write (head :: tail) w).events⟩ := by
  simp only [loop,Bind.bind,PV_EVH_Runtime.bind,h]

/-- A successful short write forwards precisely the suffix and post-state;
its prefix stays before all later events, including a later failure. -/
theorem short_write_suffix (driver : Driver) (fuel : Nat) (head : UInt8) (tail : Bytes)
    (w : State) (n : Nat)
    (h : (driver.write (head :: tail) w).outcome = .returned (.ok (.ok (n+1))))
    (hn : n+1 ≤ (head :: tail).length) :
    loop driver (fuel+1) (head :: tail) w =
      let next := loop driver fuel ((head :: tail).drop (n+1))
        (driver.write (head :: tail) w).state
      ⟨next.outcome,next.state,(driver.write (head :: tail) w).events ++ next.events⟩ := by
  simp only [loop,Bind.bind,PV_EVH_Runtime.bind,h,hn,if_true]

#print axioms empty_request
#print axioms exhausted_pending
#print axioms raw_write_fault
#print axioms short_write_suffix
end PV_EVH_WriteAll
