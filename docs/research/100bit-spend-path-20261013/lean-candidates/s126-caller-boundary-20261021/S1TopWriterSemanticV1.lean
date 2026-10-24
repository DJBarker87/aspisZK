import S1TopWriterRangesV1
import S1PrepareSemanticRootsV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareSource
open Aeneas Aeneas.Std Result VTop_Stages
open AspisS1TopPrepareCarrier AspisR1ClaimPreparedBridge
variable {CoreError W : Type}

/-- Exact lead writer prefix with the full semantic source body installed.
Root provenance and every semantic-alpha bound are derived; no independent
semantic/prepare success, parsed root value or canonicality law is assumed.
Physical compact/source child and native SDK associations remain open. -/
theorem writer_semantic (base : Ops) (sourceOps : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reserved : Bool)
    (batch : AspisR1.Port3_NativeBatchBody.Ops)
    (geometry : AspisR1.Port3_NativeGeometryBody.Ops CoreError)
    (query : AspisR1.Port3_NativeQueryBody.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : AspisR1.VTop_Provenance.WriterPrefix
      (AspisR1.Port3_NativeWriterShape.installed
        (install base (AspisR1CurrentCaller.S1SemanticInstallation.install sourceOps R B))
        reserved batch geometry query finish) D hash pub proof split none p a) :
    ∃ (zero : Top.E) (g : Array Top.E 29#usize)
      (semantic y1 : Slice U8) (view : AspisR1CurrentCaller.verifier.View)
      (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
      (pre : AspisR1PublicPreparation.r1_wire.Prefix) (payload : Slice U8) (root2 : Array U8 32#usize),
      base.op1=ok zero ∧
      prepare (AspisR1CurrentCaller.S1SemanticInstallation.install sourceOps R B)
        D pub proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) ∧
      AspisR1CurrentCaller.InstalledPreparation.sourceView proof semantic y1=ok (.Ok view) ∧
      AspisR1CurrentCaller.S1SemanticInstallation.verify R B (currentDigest D)
        (AspisS6CurrentVerifierCarrier.toPublic pub) view.semantic hash=ok (.Ok sem) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted view.semantic=ok (.Ok pre) ∧
      AspisR1PublicPreparation.FinishModel.payload pre 2#u8=ok (.Ok payload) ∧
      root2.val=payload.val ∧ p.roots=Array.make 2#usize [pre.c1_root,root2] ∧
      (∀ i : Fin 10, AspisR1CurrentCaller.S1SemanticInstallation.CanonicalQ
        (fromK (p.semantic_alpha.val[i.val]'(by simpa [p.semantic_alpha.property] using i.isLt)))) := by
  obtain ⟨zero,g,hzero,topSource⟩ := AspisR1.Port4A_PrepareCut.returned
    (install base (AspisR1CurrentCaller.S1SemanticInstallation.install sourceOps R B))
    reserved batch geometry query finish D hash pub proof split p a reached
  obtain ⟨current,currentG,source,pEq,gEq⟩ := prepare_return
    (AspisR1CurrentCaller.S1SemanticInstallation.install sourceOps R B)
    D pub proof hash (Array.repeat 29#usize zero) g p topSource
  obtain ⟨variant,semantic,y1,view,sem,pre,initial,after,challenges,payload,root2,
    hview,hsem,hnew,parsed,publicInit,begin,semanticFinish,hpayload,hcopy,hbytes,hroots,alpha,coordinates,canonical⟩ :=
    AspisR1CurrentCaller.BorrowedClaimPrepared.prepare_semantic_roots sourceOps R B (currentDigest D)
      (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash current (mapArray fromE (Array.repeat 29#usize zero)) currentG source
  refine ⟨zero,g,semantic,y1,view,sem,pre,payload,root2,hzero,topSource,hview,hsem,parsed,hpayload,hbytes,?_,?_⟩
  · rw [pEq]
    exact hroots
  · rw [pEq]
    simpa only [toPrepared,mapArray,List.getElem_map,k_round] using canonical

#print axioms writer_semantic
end AspisS1TopPrepareSource
