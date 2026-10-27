import RPu_FIr_FinishComparison
import RPu_FIq_SemanticSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_AcceptedTerminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
abbrev MainPub := AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev MQ := aspis_core.field.QM31

theorem verified {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : MainPub) (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (FIq_Terminal.install B) D pub bytes hash=ok (.Ok sem)) :
    ∃ (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
      (challenges : r1_wire.Challenges) (running terminal : MQ)
      (mask16 : Array MQ 16#usize) (mask10 : Array MQ 10#usize)
      (claim0 : Array MQ 29#usize) (claim27 mask etaTerminal masked extra28 : MQ),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      RoundModel.rounds AspisS1ExtractedRoundChildren.children (retainedDigest D) pre before=
        ok (.Ok (running,(retainedSem sem).alpha,after)) ∧
      FIq_Terminal.terminal (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub)
        (retainedSem sem).claims (retainedSem sem).alpha challenges=ok (.Ok terminal) ∧
      (S1SemanticRootCopy.install (FIq_Terminal.install B)).fromFn 16#usize
        (FinishModel.closureFn9 (retainedDigest D)) (retainedSem sem).claims=ok mask16 ∧
      (S1SemanticRootCopy.install (FIq_Terminal.install B)).fromFn 10#usize
        (FinishModel.closureFn5 (retainedDigest D)) (retainedSem sem).claims=ok mask10 ∧
      Array.index_usize (retainedSem sem).claims 0#usize=ok claim0 ∧
      Array.index_usize claim0 27#usize=ok claim27 ∧
      B.mask mask16 mask10 claim27 (retainedSem sem).alpha=ok mask ∧
      B.mul challenges.eta terminal=ok etaTerminal ∧
      B.add mask etaTerminal=ok masked ∧
      Array.index_usize (retainedSem sem).extra 28#usize=ok extra28 ∧
      B.add masked extra28=ok running := by
  obtain ⟨pre,initial,before,challenges,payload,root,parsed,publicInit,begin,finish,rest⟩ :=
    AspisR1CurrentCaller.S1SemanticInstallation.verify_roots AspisS1ExtractedRoundChildren.children
      (FIq_Terminal.install B) D pub bytes hash sem success
  obtain ⟨running,after,terminal,mask16,mask10,claim0,claim27,mask,etaTerminal,masked,extra28,
    rounds,called,m16,m10,c0,c27,maskedCall,etaCall,addCall,extraCall,finalCall⟩ :=
    FIr_FinishComparison.terminal_comparison_of_finish_success AspisS1ExtractedRoundChildren.children
      (S1SemanticRootCopy.install (FIq_Terminal.install B)) (retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre before challenges none (retainedSem sem) finish
  exact ⟨pre,before,after,challenges,running,terminal,mask16,mask10,claim0,claim27,mask,etaTerminal,masked,extra28,
    parsed,rounds,called,m16,m10,c0,c27,maskedCall,etaCall,addCall,extraCall,finalCall⟩

#print axioms verified
end AspisR1.FIr_AcceptedTerminal
end
