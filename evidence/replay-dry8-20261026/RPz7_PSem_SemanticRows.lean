import RPz7_PSem_Strict
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PSem_SemanticRows
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft

theorem source_rows (input out expanded : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (expand : AspisS1NativeCompact.compact.expand_semantic nativeValues input out=ok (.Ok (),expanded))
    (parse : AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    semanticRows 27 0 (bytesOf (input.val.drop 32))=
      some (pre.records.val.map (fun s => bytesOf s.val)) :=
  PSem_Strict.semantic_rows 27 0 _ _ (PSem_SourceRows.source_records input out expanded pre expand parse)
    (PSem_Validation.parsed_checked expanded pre parse)

/-- SemanticRows27 on the SAME physical stored proof of the accepted TX1.
This discharges the semantic-row subobligation, not transcript Aligned or the
matching-data read. No independent successful source parse is assumed. -/
theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      semanticRows 27 0 (slice (bytesOf proof.val) 48 6983)=
        some (pre.records.val.map (fun s => bytesOf s.val)) := by
  obtain ⟨stored,initial,expanded,y1,view,sem,pre,read,expand,wide,same,verify,prepare,parsed⟩ :=
    PSem_SourceCuts.parsed_prefix ops reserved query geo B std D hash pub publicBytes proof split saved run
  have frozen := source_rows stored initial expanded pre expand parsed
  have physical := PSem_Slices.range_bytes proof stored 16#usize 7031#usize read
  change stored.val=(proof.val.drop 16).take 7015 at physical
  have wire : bytesOf (stored.val.drop 32)=slice (bytesOf proof.val) 48 6983 := by
    rw [physical,List.drop_take,List.drop_drop]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  rw [wire] at frozen
  exact ⟨expanded,pre,parsed,frozen⟩

#print axioms source_rows
#print axioms on_run
end AspisR1.PSem_SemanticRows
end
