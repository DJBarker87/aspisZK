import Cons_Ten
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_Ten
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem transport {CoreError Hash : Type} {installed : AspisR1CurrentCaller.Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops CoreError}
    {D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash} {hash : Hash}
    {semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (length : proof.val.length=57607) (H : Bytes → State) (trace : List (Bytes × State)) (p : Parsed)
    (auth : ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
      (rho : OraclePortCheckpointAbiC5.K) (q : Fin 22 → Fin 262144),
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
      AuS1_Finish.Collision H trace p q ∨ ∃ recovered : Nat → Option Bytes,
        ∀ pos,pos<22 → recovered (OraclePortSelectedDraft.index q 2 pos)=
          some (OraclePortPackedChoiceC4.payload p 2 pos)) :
    Cons_Ten.Outcome run H trace p := by
  intro ports q tr data rho prepare parser read canonical domain multiply one inverse
  rcases auth data rho q prepare with collision | ⟨recovered,indexed⟩
  · exact Or.inl collision
  · exact Or.inr (Tx1Q_Endpoint.on_run installed reserved query geo D hash semantic pub proof split saved
      run length ports p q tr data rho prepare parser read recovered indexed canonical domain multiply one inverse)

#print axioms transport
end AspisR1.F3N_Ten
end
