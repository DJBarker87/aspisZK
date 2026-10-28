import NDO_JHl_SumField
import NDO_JHa_Pending
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_InitialSum
open Aeneas Aeneas.Std Result AspisR1CurrentCaller JGr_Geometry
open JHl_SumField (value)

theorem source (a : verifier.Accumulator) (call : installed.op20 .S2=ok (.Ok a))
    (j : Fin 64) : value (S7Kani3CallerTrace.initialSum
      (Port3_PendingInstall.owned (Tx1Q_Carriers.accumulator a).weights.deref)) j.val=0 := by
  have initial := (JGw_InitialFacts.source a call).1
  simp only [value,S7Kani3CallerTrace.initialSum,Port3_PendingInstall.owned,
    Port3_FlushInstall.toWeights,alloc.vec.Vec.deref,initial,List.map_replicate,
    List.getElem?_replicate,if_pos j.isLt,Option.map_some,Option.getD_some]
  rfl
#print axioms source
end AspisR1.JHl_InitialSum
end
