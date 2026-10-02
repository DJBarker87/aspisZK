import AspisR259PrivateInputRaw
import AspisV8R19.R250PrivateBaseExecution

/-! Complete private complex input, with the emitted Option try/residual
operations and source-bound enum discriminant support. -/
set_option autoImplicit false
namespace AspisV8R19.R260PrivateInputExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (CM31Exact P)
open AspisR156FullFreeze.aspis_core.field (CM31)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (C)
open AspisR259PrivateInputRaw
noncomputable section

theorem branch_none (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (none : Option T) =
      .ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Break none) := rfl

theorem branch_some {T : Type} (x : T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (some x) =
      .ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Continue x) := rfl

theorem residual_none (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T none = .ok none := by
  rfl

theorem residual_complete (T : Type) (o : Option Aeneas.Std.core.convert.Infallible) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T o = .ok none := by
  cases o with
  | none => exact residual_none T
  | some x => cases x

theorem input_complete (x : CM31) :
    circle_norm.joined_inverse.line_norm.r110_norm.C.input x =
      .ok (if x.a.val<P ∧ x.b.val<P then some (x.a,x.b) else none) := by
  by_cases ha : x.a.val<P <;> by_cases hb : x.b.val<P <;>
    simp [circle_norm.joined_inverse.line_norm.r110_norm.C.input,
      R250PrivateBaseExecution.input_complete,ha,hb,branch_none,branch_some,
      residual_none,bind_tc_ok]

theorem input_encoded (z : CM31Exact) :
    circle_norm.joined_inverse.line_norm.r110_norm.C.input
      (R163ComplexExecution.encode z) =
        .ok (some (R250PrivateBaseExecution.encodeC z)) := by
  rw [input_complete]
  simp only [R163ComplexExecution.encode,ComplexBaseExecution.encodeBase_val,
    ZMod.val_lt,and_self,if_true,R250PrivateBaseExecution.encodeC]

#print axioms branch_none
#print axioms branch_some
#print axioms residual_none
#print axioms residual_complete
#print axioms input_complete
#print axioms input_encoded
end
end AspisV8R19.R260PrivateInputExecution
