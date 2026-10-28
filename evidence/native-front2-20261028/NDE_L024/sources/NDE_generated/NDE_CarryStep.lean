import NDE_Reference7.Funs
import NDE_LiftBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace NDE_CarryStep

def toFlow (s : U64 × Usize × Bool) : ControlFlow (U64 × Usize) (Usize × Option Usize) :=
  if s.2.2 then .cont (s.1,s.2.1)
  else .done (s.2.1, if s.2.1 < 20#usize then some s.2.1 else none)

theorem step_association (index : U64) (carry : Usize) :
    NDE_LiftBridge.mapResult toFlow (NDE_Reference7.carry_step_ref index carry) =
    NDE_Reference7.carry_ref_loop.body index carry := by
  unfold NDE_Reference7.carry_step_ref NDE_Reference7.carry_ref_loop.body
  split
  · rename_i h
    simp only [lift, bind_tc_ok]
    split
    · simp [NDE_LiftBridge.mapResult,toFlow,h]
    · cases index >>> 1#u32 <;> first
      | rfl
      | (cases carry + 1#usize <;> rfl)
  · rename_i h
    simp [NDE_LiftBridge.mapResult,toFlow,h]

#print axioms step_association
end NDE_CarryStep
