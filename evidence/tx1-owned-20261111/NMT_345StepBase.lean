import NMT_345Carriers
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
/-- Unreached fields are panic-valued. Every reached field is replaced by its
CLOSED concrete interpretation; this is not a free Ops premise. -/
def baseOps : AdapterRw.Ops := by
 constructor <;> intros <;> exact .fail .panic
/-- Exact emitted `?`: all outer and inner Results, including stops. -/
def tryStep {A : Type} (r : Result (core.result.Result A PE))
 (next : A → Result Ret) : Result Ret := do
 let value ← r
 match value with
 | .Ok a => next a
 | .Err e => .ok (.Err e)

theorem emitted_try {A : Type} (r : Result (core.result.Result A PE))
 (next : A → Result Ret) :
 (do
  let value ← r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch value
  match cf with
  | core.ops.control_flow.ControlFlow.Continue a => next a
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec U8) (core.convert.FromSame PE) residual) = tryStep r next := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok value => cases value <;> rfl

/-- The parent state survives a pure successful child exactly; an error or
stopped child never runs the suffix. -/
theorem tryStep_complete {A : Type} (r : Result (core.result.Result A PE))
 (next : A → Result Ret) : tryStep r next =
 match r with
 | .ok (.Ok a) => next a
 | .ok (.Err e) => .ok (.Err e)
 | .fail e => .fail e
 | .div => .div := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok value => cases value <;> rfl
#print axioms emitted_try
#print axioms tryStep_complete
end NMT_345
