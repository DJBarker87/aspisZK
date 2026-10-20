import AspisR1Libra.Funs
import CuSavingsArrayFromFn

/-! Kernel checked signature transport for the actual emitted mutable closures.
The raw call_mut bodies and the producer-emitted call_once bodies are retained.
The backend FnMut instance uses call_once, which applies the raw handback before
passing updated closure state to the next builder iteration. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.CuSavingsLibraSourceHandback
open AspisR1Libra
variable [Shared]

theorem power_callback {N : Usize} (c : kpowers.closure N) (i : Usize) :
    kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once c i =
      (do
        let (value,updated,back) ←
          kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut c i
        .ok (value,back updated)) := by
  unfold kpowers.closure at c ⊢
  rcases c with ⟨power,q⟩
  unfold kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [kpowers.closure]
  try dsimp only
  cases h : field.QM31.mul power q <;>
    simp only [kpowers.closure,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem reference_power_callback
    (c : old.twofold_libra_weights.closure.closure) (i : Usize) :
    old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once c i =
      (do
        let (value,updated,back) ←
          old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut c i
        .ok (value,back updated)) := by
  unfold old.twofold_libra_weights.closure.closure at c ⊢
  rcases c with ⟨power,extra,side⟩
  unfold old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [old.twofold_libra_weights.closure.closure]
  try dsimp only
  cases hi : Array.index_usize extra side with
  | fail e => simp only [old.twofold_libra_weights.closure.closure,hi,bind_tc_fail]
  | div => simp only [old.twofold_libra_weights.closure.closure,hi,bind_tc_div]
  | ok q =>
    simp only [old.twofold_libra_weights.closure.closure,hi,bind_tc_ok]
    cases hm : field.QM31.mul power q <;> simp only [hm,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem mutable_builder_projection {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) :
    (do let (array,_) ← AspisR1Libra.core.array.from_fn_mut N inst state
        .ok array) = AspisR1.CuSavingsArrayBuilder.build N inst state := by
  unfold AspisR1Libra.core.array.from_fn_mut AspisR1.CuSavingsArrayBuilder.build
  cases h : AspisR1.CuSavingsArrayBuilder.cells inst N.val 0#usize state <;> rfl

theorem array_source_admission {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) :
    AspisR1CuArrayGraph.core.array.from_fn N inst state =
      AspisR1.CuSavingsArrayBuilder.build N inst state :=
  CuSavingsArrayFromFn.source_eq_build N inst state

#print axioms array_source_admission
#print axioms power_callback
#print axioms reference_power_callback
#print axioms mutable_builder_projection
end AspisR1.CuSavingsLibraSourceHandback
