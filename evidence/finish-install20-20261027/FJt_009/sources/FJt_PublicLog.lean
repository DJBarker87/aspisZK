import FJt_PrepareHead
import FJt_SamplerHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_PublicLog
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

theorem value (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (accepted : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input=ok (.Ok p,scratch))
    (H : Bytes → State) (pf : RawCutProverCompiler.Proof) (literal : LiteralTranscript.Public)
    (parsed : Parsed)
    (aligned : Aligned parsed (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix literal))).2))
    (logs : AuS1_Recovery.log ops B std D pub proof hash input=
      (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix literal))).1) :
    ∃ encoded : alloc.vec.Vec U8,
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic pub)=ok (.Ok encoded) ∧
      literal.pubBytes=AspisR1PublicPreparation.SourceDigestAddresses.rawBytes encoded.deref := by
  obtain ⟨encoded,root,state,serialized,head⟩:=FJt_PrepareHead.value ops B std D pub proof hash p input scratch accepted
  obtain ⟨r,c,initial,bytesEq⟩:=aligned.2.2.2.1
  obtain ⟨challenge,called⟩:=F3L_SamplerMessages.entry H pf literal 33 0 (by decide)
  have erased:=F3L_EraseIndex.entry _ 0 (pf 0) challenge called
  have first:=(Prod.mk.inj (Option.some.inj (erased.symm.trans initial))).1
  have sampler:=FJt_SamplerHead.head H pf literal r first
  rw [logs,sampler] at head
  have pair:=Option.some.inj head
  exact ⟨encoded,serialized,F3T_InitFrame.public_bytes _ _ _ _ (congrArg Prod.fst pair).symm⟩
#print axioms value
end AspisR1.FJt_PublicLog
end
