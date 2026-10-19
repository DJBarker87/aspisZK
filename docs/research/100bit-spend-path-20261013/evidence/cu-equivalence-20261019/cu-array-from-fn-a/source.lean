import CuSavingsArraySourceBuilder

/-! Consuming theorem: the complete emitted from_fn, including its source
wrapper, equals the callback builder used by the dot-kernel comparison.
Primitive/frontend admission remains explicit in the imported model. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayFromFn
open Aeneas Aeneas.Std Result
open CuSavingsArrayBuilder CuSavingsArraySourceBuilder

abbrev wrapped {T F : Type} (inst : core.ops.function.FnMut F Usize T) :=
  AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit inst

theorem wrapped_call {T F : Type} (inst : core.ops.function.FnMut F Usize T)
    (state : F) (index : Usize) :
    remap (fun (value,state1) => (value,id state1)) ((wrapped inst).call_mut state index) =
      inst.call_mut (id state) index := by
  cases h : inst.call_mut state index with
  | fail e => simp only [wrapped,
      AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit,
      AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit.call_mut,h,bind_tc_fail,remap,id_eq]
  | div => simp only [wrapped,
      AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit,
      AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit.call_mut,h,bind_tc_div,remap,id_eq]
  | ok pair => rcases pair with ⟨value,state1⟩;simp only [wrapped,
      AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit,
      AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1.closure.Insts.CoreOpsFunctionFnMutTupleANeverShortCircuit.call_mut,h,bind_tc_ok,uncurry_apply_pair,remap,id_eq]

theorem source_eq_build {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) :
    AspisR1CuArrayGraph.core.array.from_fn N inst state = build N inst state := by
  unfold AspisR1CuArrayGraph.core.array.from_fn
  simp only [AspisR1CuArrayGraph.core.ops.try_trait.NeverShortCircuit.wrap_mut_1,bind_tc_ok]
  trans build N (wrapped inst) state
  · exact try_eq_build N (wrapped inst) state
  exact build_naturality (wrapped inst) inst id (wrapped_call inst) N state

#print axioms wrapped_call
#print axioms source_eq_build
end AspisR1.CuSavingsArrayFromFn
