import PSem_SemanticRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_Parser
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open MultiproofConeCanonical OraclePortCompactDraft

def Facts (proof : Slice U8) : Prop :=
  ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) ∧
    semanticRows 27 0 (slice (bytesOf proof.val) 48 6983) =
      some (pre.records.val.map (fun s => bytesOf s.val)) ∧
    parse (bytesOf proof.val) = some ⟨bytesOf proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩

theorem on_run {C H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (header : OraclePortHeader.accepts (bytesOf proof.val) = true)
    (scanned : scan (bytesOf proof.val)) : Facts proof := by
  obtain ⟨expanded,pre,parsed,rows⟩ :=
    PSem_SemanticRows.on_run ops reserved query geo B std D hash pub publicBytes proof split saved run
  exact ⟨expanded,pre,parsed,rows,by simp [parse,header,scanned,rows]⟩

#print axioms on_run
end AspisR1.T2R_Parser
end
