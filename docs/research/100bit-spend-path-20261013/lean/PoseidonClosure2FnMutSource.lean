import PoseidonProjectedClosure2Source

set_option autoImplicit false
namespace AspisR1PoseidonProjectedClosure2Source
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    (c : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
    (i : Usize) : Result field.QM31 := do
  let (q, _) ←
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut c i
  ok q

@[reducible]
def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    : core.ops.function.FnOnce
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2 Usize field.QM31 := {
  call_once :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

@[reducible]
def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    : core.ops.function.FnMut
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2 Usize field.QM31 := {
  FnOnceInst :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

end AspisR1PoseidonProjectedClosure2Source
