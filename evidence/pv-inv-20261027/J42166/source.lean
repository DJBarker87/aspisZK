import Mathlib.Data.List.Basic
set_option autoImplicit false
namespace R1Z.PV_Inv_ZeroTraceLimit
/-- Source-expression observation of short-circuit limb tests. This concerns
the research source predicates, not an assertion about adopted CT machine code. -/
def limbTests : List Nat → List Bool
  | [] => []
  | x::xs => if x=0 then true::limbTests xs else [false]

theorem same_nonzero_verdict_different_prefix :
    ([0,1,0,0] : List Nat) ≠ [0,0,0,0] ∧
    ([1,0,0,0] : List Nat) ≠ [0,0,0,0] ∧
    limbTests [0,1,0,0] ≠ limbTests [1,0,0,0] := by
  decide

#print axioms same_nonzero_verdict_different_prefix
end R1Z.PV_Inv_ZeroTraceLimit
