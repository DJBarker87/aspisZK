import FJq_MaskedMain
import FJt_AlphaOnRun
import FJq_AcceptedExtra
import FJn_BeginCanonical
import FIr_AlphaCanonical
import FIq_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_AcceptedMaskedMain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open FIp_SemanticValues (Canon decode)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.Mask.terminalZ FIq_Terminal.terminal
/-- ONE accepted call of the explicit FIq installation yields the complete
masked running VALUE. This does not specialize the adopted FIp callback. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops) (seed : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native (FirstComposition.toRetainedPublic pub)))
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std (FIq_Install.boundaries seed))).op9 D pub bytes hash none=ok (.Ok sem)) :
    ∃ (pre : AspisR1PublicPreparation.r1_wire.Prefix) (before after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (c : AspisR1PublicPreparation.r1_wire.Challenges) (running : AspisR1PublicPreparation.aspis_core.field.QM31),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      (retainedSem sem).challenges=c ∧
      RoundModel.rounds AspisS1ExtractedRoundChildren.children (retainedDigest D) pre before=
        ok (.Ok (running,(retainedSem sem).alpha,after)) ∧
      Canon running ∧ embed (decode running)=
        R0P.Mask.terminalZ (R0P.Mask.maskClaimsR0 ConcretePackBasis.basis)
          (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic
            (FJa_PublicCopy.native (FirstComposition.toRetainedPublic pub))))
          (embed (decode c.lambda)) (embed (decode c.chi)) (embed (decode c.theta))
          (embed (decode c.mu)) (embed (decode c.eta))
          (fun i=>embed (FJn_MainPoint.point c.zc i)) ConcretePackBasis.basis
          (fun j l=>embed (FJn_MainClaims.claims (retainedSem sem).claims j l))
          (fun l=>embed (decode (FJq_MainCells.cell (retainedSem sem).extra l)))
          (fun i=>embed (FJn_MainPoint.point (retainedSem sem).alpha i)) := by
  obtain ⟨pre,t0,before,c,parsed,publicInit,begun,finished,claims⟩:=
    ClaimsUnrolledSdk.semantic_claims std ops (FIq_Install.boundaries seed) D pub bytes hash sem accepted
  have canonClaims:=FJa_ClaimsOnRun.value std ops (FIq_Install.boundaries seed) D pub bytes hash sem accepted
  have canonAlpha:=FJt_AlphaOnRun.value std ops (FIq_Install.boundaries seed) D pub bytes hash sem accepted
  obtain ⟨extraPre,record,extraParsed,extraRead,extraDecode,canonExtra⟩:=
    FJq_AcceptedExtra.value std ops (FIq_Install.boundaries seed) D pub bytes hash sem accepted
  obtain ⟨hl,hchi,ht,hm,he,hz⟩:=FJn_BeginCanonical.value (retainedDigest D) pre t0 before c begun
  obtain ⟨r,t25,r25,r26,z0,t26,z1,t27,rounds0,challengeEq,rest⟩:=
    S1SemanticFinishBounds.finish_success AspisS1ExtractedRoundChildren.children
      (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std (FIq_Install.boundaries seed)))
      (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre before c none (retainedSem sem) finished
  obtain ⟨running,after,terminal,c1,m,row,g,mask,product,sum,x,
    rounds,terminalCall,rc,rm,rr,rg,maskCall,multiply,add,rx,finish⟩:=
    FIr_FinishComparison.terminal_comparison_of_finish_success AspisS1ExtractedRoundChildren.children
      (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std (FIq_Install.boundaries seed)))
      (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre before c none (retainedSem sem) finished
  have result:=FJq_MaskedMain.value (retainedDigest D) (FirstComposition.toRetainedPublic pub)
    (retainedSem sem).claims (retainedSem sem).alpha (retainedSem sem).extra c c1 m row g terminal x mask product sum running
    canonClaims canonAlpha canonExtra hz hl hchi ht hm he bounds terminalCall rc rm rr rg rx maskCall multiply add finish
  exact ⟨pre,before,after,c,running,parsed,challengeEq,rounds,result.1,result.2⟩
#print axioms value
end AspisR1.FJt_AcceptedMaskedMain
end
