import S1TopWriterSemanticV1
import S1NativePreparePhysicalRootsV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareSource
open Aeneas Aeneas.Std Result VTop_Stages
open AspisS1TopPrepareCarrier AspisR1ClaimPreparedBridge
variable {CoreError W : Type}

/-- The lead's exact writer prefix now derives both physical root byte
identities from its same full op7 preparation. The Y1 length law remains
explicit; no independent prepare/semantic/parser/expansion or root-binding
premise is supplied. Native SDK/callee and other Prepared fields remain open. -/
theorem writer_physical_roots (base : Ops) (sourceOps : AspisR1CurrentCaller.Ops)
    (native : AspisS1NativeCompact.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (valueLength : ∀ input output status updated,
      sourceOps.op11 input output=ok (status,updated) → updated.length=output.length)
    (reserved : Bool) (batch : AspisR1.Port3_NativeBatchBody.Ops)
    (geometry : AspisR1.Port3_NativeGeometryBody.Ops CoreError)
    (query : AspisR1.Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : AspisR1.VTop_Provenance.WriterPrefix
      (AspisR1.Port3_NativeWriterShape.installed
        (install base (AspisR1CurrentCaller.S1SemanticInstallation.install
          {sourceOps with op10:=AspisS1NativeCompact.compact.expand_semantic native} R B))
        reserved batch geometry query finish) D hash pub proof split none p a) :
    ∃ (root0 root1 : Array U8 32#usize),
      p.roots=Array.make 2#usize [root0,root1] ∧
      root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 := by
  obtain ⟨zero,g,hzero,topSource⟩ := AspisR1.Port4A_PrepareCut.returned
    (install base (AspisR1CurrentCaller.S1SemanticInstallation.install
      {sourceOps with op10:=AspisS1NativeCompact.compact.expand_semantic native} R B))
    reserved batch geometry query finish D hash pub proof split p a reached
  obtain ⟨current,currentG,source,pEq,gEq⟩ := prepare_return
    (AspisR1CurrentCaller.S1SemanticInstallation.install
      {sourceOps with op10:=AspisS1NativeCompact.compact.expand_semantic native} R B)
    D pub proof hash (Array.repeat 29#usize zero) g p topSource
  obtain ⟨root0,root1,hroots,hphysical0,hphysical1⟩ :=
    AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers.prepare_physical_roots
      sourceOps native R B valueLength (currentDigest D) (AspisS6CurrentVerifierCarrier.toPublic pub)
      proof hash current (mapArray fromE (Array.repeat 29#usize zero)) currentG source
  refine ⟨root0,root1,?_,hphysical0,hphysical1⟩
  rw [pEq]
  exact hroots

#print axioms writer_physical_roots
end AspisS1TopPrepareSource
