import PV_EVH_WriteAll
set_option autoImplicit false
namespace PV_EVH_LiteralWriteAll
open Aeneas Aeneas.Std PV_EVH_Runtime
open PV_EVH_WriteAll (Driver loop)
open PV_RJ4IDB (Bytes)

/-- ErrorKind inspection, interrupted-error drop, and any following retry are
world operations of the retained driver, never pure classification assumptions. -/
theorem error_dispatch (driver : Driver) (fuel : Nat) (head : UInt8) (tail : Bytes)
    (w : State) (e : driver.Error)
    (h : (driver.write (head :: tail) w).outcome = .returned (.ok (.error e))) :
    loop driver (fuel+1) (head :: tail) w =
      let next : PV_EVH_Runtime.Run (Except driver.Error Unit) := (do
        let retry ← driver.interrupted e
        if retry then do
          let _ ← driver.dropInterrupted e
          loop driver fuel (head :: tail)
        else pure (.error e)) (driver.write (head :: tail) w).state
      ⟨next.outcome,next.state,(driver.write (head :: tail) w).events ++ next.events⟩ := by
  simp only [PV_EVH_WriteAll.loop,Bind.bind,PV_EVH_Runtime.bind,h]

/-- WriteZero construction is retained as a runtime operation. This does not
assert a silent constructor or erase allocation/destructor behaviour. -/
theorem zero_dispatch (driver : Driver) (fuel : Nat) (head : UInt8) (tail : Bytes)
    (w : State)
    (h : (driver.write (head :: tail) w).outcome = .returned (.ok (.ok 0))) :
    loop driver (fuel+1) (head :: tail) w =
      let next : PV_EVH_Runtime.Run (Except driver.Error Unit) := (do let e ← driver.writeZero; pure (.error e))
        (driver.write (head :: tail) w).state
      ⟨next.outcome,next.state,(driver.write (head :: tail) w).events ++ next.events⟩ := by
  simp only [PV_EVH_WriteAll.loop,Bind.bind,PV_EVH_Runtime.bind,h]

#print axioms error_dispatch
#print axioms zero_dispatch
end PV_EVH_LiteralWriteAll
