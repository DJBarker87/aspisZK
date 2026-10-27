import T2R_Ten
import Cons_Ten
import Tx1Q_Endpoint
import AuS1_Finish
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.T2R_LegacyTen
open Tx1Q_Carriers AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
theorem forget {CoreError H : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H} {hash : H}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : Parsed)
    (new : T2R_Ten.Outcome run H trace parsed) : Cons_Ten.Outcome run H trace parsed := by
  intro ports q tr data rho prepare parser read canonical domain multiply one inverse
  exact new ports q tr data rho prepare read canonical domain multiply one inverse

#print axioms forget
end AspisR1.T2R_LegacyTen
end
