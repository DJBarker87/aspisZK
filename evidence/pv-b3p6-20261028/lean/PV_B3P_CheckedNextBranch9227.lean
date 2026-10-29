import PV_B3P_P227_08
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem checked_next_overflow9 (index next : U64) (h : U64.checked_add index 1#u64 = none) :
    reference_terminal.checked_next227 index next = .ok true := by
  simp only [reference_terminal.checked_next227,h,lift,bind_tc_ok]

theorem checked_next_success9 (index next value : U64)
    (h : U64.checked_add index 1#u64 = some value) :
    reference_terminal.checked_next227 index next = .ok (value != next) := by
  simp only [reference_terminal.checked_next227,h,lift,bind_tc_ok]

theorem option_ne_some9 (value : Option U64) (next : U64) :
    (match value with | none => true | some x => x != next) = (value != some next) := by
  cases value <;> rfl

#print axioms checked_next_overflow9
#print axioms checked_next_success9
#print axioms option_ne_some9
end PV_B3P_Binding9227
