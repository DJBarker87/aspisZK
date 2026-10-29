import PV_L1C_Prefix
/-! Countermodels to invalid proof inferences, NOT native privacy findings. -/
set_option autoImplicit false
namespace PV_L1C
open PV_RJ4IDB

def orderLeft : NativeTrace Unit := ⟨[.count 1,.wall []],.failure []⟩
def orderRight : NativeTrace Unit := ⟨[.wall [],.count 1],.failure []⟩

/-- Even ALL FOUR exact typed component inputs can hold against the other
trace, while the retained joint observer distinguishes their event order. -/
theorem four_inputs_do_not_fix_order :
 OpenInputs.L1_COUNT_TRACE
   (fun _ : Unit => (nativeCounts orderLeft.events,nativeRejections orderLeft.events))
   (fun _ => orderRight) ∧
 OpenInputs.L1_TIME_TRACE (fun _ : Unit => nativeTimes orderLeft.events) (fun _ => orderRight) ∧
 OpenInputs.L1_ORACLE_PREFIX (fun _ : Unit => nativeOracle orderLeft.events) (fun _ => orderRight) ∧
 OpenInputs.L1_RETAINED_SIDECHANNELS
   (fun _ : Unit => nativeSide orderLeft.events) (fun _ => orderRight) ∧
 nativeObservation orderLeft ≠ nativeObservation orderRight := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · intro i; rfl
 · intro i; rfl
 · intro i; rfl
 · intro i; rfl
 · intro h
   have he := congrArg Observation.ordered h
   change [Event.attempts 1,Event.proveWallSeconds []] =
     [Event.proveWallSeconds [],Event.attempts 1] at he
   cases he

/-- A duplicate is retained as a second query, including on a failure prefix. -/
theorem duplicate_failure_prefix (a b : Bytes) :
 nativeOracle ([.oracle a b,.oracle a b] : List NativeEvent) = [(a,b),(a,b)] := rfl

/-- The terminal tag never erases a previously observed oracle prefix. -/
theorem terminal_does_not_erase (es : List NativeEvent) (t : Terminal Unit) :
 (nativeObservation (⟨es,t⟩ : NativeTrace Unit)).queryPrefix = nativeOracle es := rfl

#print axioms four_inputs_do_not_fix_order
#print axioms duplicate_failure_prefix
#print axioms terminal_does_not_erase
end PV_L1C
