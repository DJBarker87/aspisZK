import PSem_Root
import PSem_SemanticRows
import PSem_SemanticTrace
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_SourceTrace

def storedRoot (proof : Slice U8) : List U8 := (proof.val.drop 16).take 32
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft

theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (expanded : Slice U8) (sem : r1_semantic.Verified H) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (t0 t25 : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (cs : List (AspisR1PublicPreparation.SourceFull25.Call (retainedDigest D) pre)),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      semanticRows 27 0 (slice (bytesOf proof.val) 48 6983)=
        some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest D)
        (FirstComposition.toRetainedPublic pub) hash pre.c1_root=ok (.Ok t0) ∧
      pre.c1_root.val=storedRoot proof ∧
      AspisR1PublicPreparation.SourceFull25.Trace (retainedDigest D) pre t0 t25 cs ∧
      cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map (fun c => bytesOf c.record.framed.val)=
        (pre.records.val.map (fun s => bytesOf s.val)).take 25 ∧
      ∃ record25 record26 z0 t26 z1 t27,
        AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record25) ∧
        AspisR1PublicPreparation.FinishModel.circle_validated
          (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest D) t25 record25=ok (.Ok z0,t26) ∧
        AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
        AspisR1PublicPreparation.FinishModel.circle_validated
          (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest D) t26 record26=ok (.Ok z1,t27) ∧
        (retainedSem sem).transcript=t27 := by
  obtain ⟨stored,initial,expanded,y1,view,sem,pre,read,expand,wide,same,verify,prepare,parsed⟩ :=
    PSem_SourceCuts.parsed_prefix ops reserved query geo B std D hash pub publicBytes proof split saved run
  have frozen := PSem_SemanticRows.source_rows stored initial expanded pre expand parsed
  have physical := PSem_Slices.range_bytes proof stored 16#usize 7031#usize read
  change stored.val=(proof.val.drop 16).take 7015 at physical
  have wire : bytesOf (stored.val.drop 32)=slice (bytesOf proof.val) 48 6983 := by
    rw [physical,List.drop_take,List.drop_drop]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  rw [wire] at frozen
  obtain ⟨pre',t0,t15,t25,cs,parsed',publicInit,trace,rows,frames,circles⟩ :=
    PSem_SemanticTrace.verify_calls AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub expanded hash sem verify
  have eq : pre'=pre := core.result.Result.Ok.inj (Result.ok.inj (parsed'.symm.trans parsed))
  subst pre'
  have root := PSem_Root.source_root stored initial expanded pre expand parsed
  have rootPhysical : pre.c1_root.val=storedRoot proof := by
    rw [root,physical]
    simp only [storedRoot,List.take_take]
    rfl
  refine ⟨expanded,sem,pre,t0,t25,cs,parsed,frozen,publicInit,rootPhysical,trace,rows,?_,circles⟩
  have mapped := congrArg (List.map (fun s : Slice U8 => bytesOf s.val)) frames
  simpa only [List.map_map,List.map_take,Function.comp_def] using mapped

#print axioms on_run
end AspisR1.PAln_SourceTrace
end
