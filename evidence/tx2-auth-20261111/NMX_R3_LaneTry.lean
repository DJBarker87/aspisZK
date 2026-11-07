import NMX_R3_LaneObserve
set_option autoImplicit false
namespace NMX_R3_LaneTry
open Aeneas Aeneas.Std Result NMX_R3_LaneObserve

def question {A : Type} (read : Result (core.result.Result A Unit))
 (next : A → Result Native) : Result Native := do
 let r ← read
 match r with
 | .Ok a => next a
 | .Err () => ok (.Err ())

def option {A B : Type} (f : A → B) : core.result.Result A Unit → Option B
 | .Ok a => some (f a)
 | .Err () => none

/-- One source `?` occurrence, all native result/failure/divergence arms. -/
theorem source {A : Type} (read : Result (core.result.Result A Unit)) (next : A → Result Native) :
 (do let r ← read
     let cf ← core.result.Result.Insts.CoreOpsTry.branch r
     match cf with
     | core.ops.control_flow.ControlFlow.Continue a => next a
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        NCV_Reference.Lane (core.convert.FromSame Unit) residual) = question read next := by
 cases read with
 | fail e => rfl
 | div => rfl
 | ok r => cases r with
   | Ok a => rfl
   | Err u => cases u; rfl

/-- Fold before any concrete array or recursive model is substituted. -/
theorem fold {A B : Type} (read : Result (core.result.Result A Unit))
 (r : core.result.Result A Unit) (f : A → B) (model : Option B)
 (next : A → Result Native) (modelNext : B → Option RSL.LaneState)
 (call : read = ok r) (mapped : option f r = model)
 (continuation : ∀ a, observe (next a) = ok (modelNext (f a))) :
 observe (question read next) = ok (model.bind modelNext) := by
 rw [call, ← mapped]
 cases r with
 | Ok a => exact continuation a
 | Err u => cases u; rfl
#print axioms source
#print axioms fold
end NMX_R3_LaneTry
