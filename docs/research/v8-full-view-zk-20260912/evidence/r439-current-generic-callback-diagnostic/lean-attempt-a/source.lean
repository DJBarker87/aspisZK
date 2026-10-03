import AspisV8R19.R174GammaBatchStep

/-! Current generic FnMut dictionary and callback, extracted from R438 via the
R439 declaration-selection diagnostic. The four source declarations below
retain all bodies and dictionary fields; only declaration names and qualification
to the previously proved same-source field providers change.
This does not establish the caller's borrow construction, fold instantiation,
outside frame, slice iterator, callback chronology, or end-to-end security. -/
set_option autoImplicit false
namespace AspisV8R19.R439CurrentGammaFnMut
open Aeneas Aeneas.Std Result

/-- [aspis_v8_performance_host::freeze::closure#2::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_v8_performance_host::freeze::closure#2::closure<'_0, '_1>}::call_mut]:
    Source: '../relation_callback.rs', lines 134:62-134:108 -/
def
  currentCallMut
  (c : AspisR156FullFreeze.freeze.closure_2.closure)
  (tupled_args : (AspisR156FullFreeze.aspis_core.field.QM31 × AspisR156FullFreeze.aspis_core.field.QM31)) :
  Result (AspisR156FullFreeze.aspis_core.field.QM31 × AspisR156FullFreeze.freeze.closure_2.closure ×
    (AspisR156FullFreeze.freeze.closure_2.closure → AspisR156FullFreeze.freeze.closure_2.closure))
  := do
  let (q, q1) := c
  let (a, v) := tupled_args
  let q2 ← AspisR156FullFreeze.aspis_core.field.QM31.mul q v
  let r ← AspisR156FullFreeze.aspis_core.field.QM31.add a q2
  let q3 ← AspisR156FullFreeze.aspis_core.field.QM31.mul q q1
  let back := fun c1 => let (q4, _) := c1
                        (q4, q1)
  ok (r, (q3, q1), back)

/-- [aspis_v8_performance_host::freeze::closure#2::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_v8_performance_host::freeze::closure#2::closure<'_0, '_1>}::call_once]:
    Source: '../relation_callback.rs', lines 134:62-134:108 -/
def
  currentCallOnce
  (c : AspisR156FullFreeze.freeze.closure_2.closure)
  (p : (AspisR156FullFreeze.aspis_core.field.QM31 × AspisR156FullFreeze.aspis_core.field.QM31)) :
  Result (AspisR156FullFreeze.aspis_core.field.QM31 × AspisR156FullFreeze.freeze.closure_2.closure)
  := do
  let (_, q) := c
  let (q1, c1, call_mut_back) ←
    currentCallMut
      c p
  let (q2, _) := call_mut_back c1
  ok (q1, (q2, q))

/-- Trait implementation: [aspis_v8_performance_host::freeze::closure#2::{impl core::ops::function::FnOnce<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_v8_performance_host::freeze::closure#2::closure<'_0, '_1>}]
    Source: '../relation_callback.rs', lines 134:62-134:108 -/
@[reducible]
def currentFnOnce
  : core.ops.function.FnOnce AspisR156FullFreeze.freeze.closure_2.closure (AspisR156FullFreeze.aspis_core.field.QM31 ×
  AspisR156FullFreeze.aspis_core.field.QM31) AspisR156FullFreeze.aspis_core.field.QM31 := {
  call_once :=
    currentCallOnce
}

/-- Trait implementation: [aspis_v8_performance_host::freeze::closure#2::{impl core::ops::function::FnMut<(aspis_core::field::QM31, &'_ aspis_core::field::QM31), aspis_core::field::QM31> for aspis_v8_performance_host::freeze::closure#2::closure<'_0, '_1>}]
    Source: '../relation_callback.rs', lines 134:62-134:108 -/
@[reducible]
def currentFnMut :
  core.ops.function.FnMut AspisR156FullFreeze.freeze.closure_2.closure (AspisR156FullFreeze.aspis_core.field.QM31 ×
  AspisR156FullFreeze.aspis_core.field.QM31) AspisR156FullFreeze.aspis_core.field.QM31 := {
  FnOnceInst :=
    currentFnOnce
  call_mut :=
    currentCallMut
}


abbrev QM31 := AspisR156FullFreeze.aspis_core.field.QM31
abbrev Closure := AspisR156FullFreeze.freeze.closure_2.closure

theorem selected_call_binding (c : Closure) (args : QM31 × QM31) :
    currentFnMut.call_mut c args = R174GammaBatchStep.rawCallMut c args := rfl

theorem selected_closed (power gamma acc value : QM31) :
    AspisV8R17.MaskClosureWriteback.finishCall
      (currentFnMut.call_mut (power, gamma) (acc, value)) = (do
      let weighted ← AspisR156FullFreeze.aspis_core.field.QM31.mul power value
      let total ← AspisR156FullFreeze.aspis_core.field.QM31.add acc weighted
      let next ← AspisR156FullFreeze.aspis_core.field.QM31.mul power gamma
      ok (total, (next, gamma))) := by
  rw [selected_call_binding]
  exact R174GammaBatchStep.rawCallMut_closed power gamma acc value

theorem selected_encoded_closed
    (power gamma acc value : AspisV8R15.ExactTowerBase.QM31Exact) :
    AspisV8R17.MaskClosureWriteback.finishCall
      (currentFnMut.call_mut
        (R164ProductExecution.encode power, R164ProductExecution.encode gamma)
        (R164ProductExecution.encode acc, R164ProductExecution.encode value)) =
      .ok (R164ProductExecution.encode (acc + power * value),
        (R164ProductExecution.encode (power * gamma),
          R164ProductExecution.encode gamma)) := by
  rw [selected_call_binding]
  exact R174GammaBatchStep.encoded_closed power gamma acc value

theorem selected_encoded_raw
    (power gamma acc value : AspisV8R15.ExactTowerBase.QM31Exact) :
    currentFnMut.call_mut
      (R164ProductExecution.encode power, R164ProductExecution.encode gamma)
      (R164ProductExecution.encode acc, R164ProductExecution.encode value) =
      .ok (R164ProductExecution.encode (acc + power * value),
        (R164ProductExecution.encode (power * gamma), R164ProductExecution.encode gamma),
        fun c1 => let (q4, _) := c1
                  (q4, R164ProductExecution.encode gamma)) := by
  rw [selected_call_binding]
  simp only [R174GammaBatchStep.rawCallMut, R164ProductExecution.public_product,
    R165QuarticExecution.add, bind_tc_ok]

theorem selected_backward_restores_capture
    (power gamma acc value : AspisV8R15.ExactTowerBase.QM31Exact)
    (replacementPower replacementGamma : QM31) :
    (do
      let (_, _, back) ← currentFnMut.call_mut
        (R164ProductExecution.encode power, R164ProductExecution.encode gamma)
        (R164ProductExecution.encode acc, R164ProductExecution.encode value)
      ok (back (replacementPower, replacementGamma))) =
        .ok (replacementPower, R164ProductExecution.encode gamma) := by
  rw [selected_encoded_raw]
  rfl

#print axioms selected_call_binding
#print axioms selected_closed
#print axioms selected_encoded_closed
#print axioms selected_encoded_raw
#print axioms selected_backward_restores_capture
end AspisV8R19.R439CurrentGammaFnMut
