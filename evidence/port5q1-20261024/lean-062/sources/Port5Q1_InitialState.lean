import Port4C_Pending
import Port4C_QueryState
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_InitialState
open Aeneas Aeneas.Std AspisR1Stage2

theorem state (a : verifier.Accumulator) (size : a.weights.val.length=64) :
    Port4C_QueryState.state a
      (S7Kani3CallerTrace.initialSum (Port3_PendingInstall.owned a.weights.deref))=
      CheckpointBytes5Output.accumulator a := by
  unfold Port4C_QueryState.state CheckpointBytes5Output.accumulator
  congr 1
  funext i
  have hi : i.val<a.weights.val.length := by rw [size]; exact i.isLt
  rw [List.getElem?_eq_getElem hi,Option.getD_some,Port4C_SumField.source_words]
  unfold Port4C_SumField.weight S7Kani3CallerTrace.initialSum Port3_PendingInstall.owned
    Port3_FlushInstall.toWeights
  simp only [alloc.vec.Vec.deref,List.getElem?_map,List.getElem?_eq_getElem hi,
    Option.map_some,Option.getD_some]
  rfl

#print axioms state
end AspisR1.Port5Q1_InitialState
end
