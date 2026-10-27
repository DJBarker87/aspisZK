import RPt_FJl_LoopExtraction
import RPz7_Tx1Q_Execution
import RPz7_Tx1Q_Initial
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_Tx1Extraction
open Aeneas Aeneas.Std Result AspisR1Stage2
open Tx1Q_Carriers
/-- Calls 0..9 come from this accepted TX1 witness, with its own prepared/scratch. -/
theorem reached {C H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (j : Fin 10) :
    ∃ a0 a1 b0 b1, a0.next.val=j.val ∧
      Port3_NativeQueryBody.verifier.candidate.query_values (Tx1Q_QueryBridge.leaves query)
        proof (prepared run.p) a0 (arr e run.scratch) none (geometry run.geometry) b0=ok (.Ok (a1,b1)) := by
  have start := (Tx1Q_Initial.fields reserved (accumulator run.initial) run.initial_call).2.1
  exact FJl_LoopExtraction.native _ proof _ _ _ _ none _ _ _ 10#usize
    (by rw [start]; decide) run.query_call j.val (by rw [start]; exact Nat.zero_le _) j.isLt
#print axioms reached
end AspisR1.FJl_Tx1Extraction
end
