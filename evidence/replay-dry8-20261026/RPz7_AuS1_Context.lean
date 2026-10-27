import RPz7_AuS1_Recovery
import RPz7_SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Context
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.AdaptiveFirstReadLaw
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

 theorem authenticated (prior : Program Bytes State Unit) (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (source : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8)
    (hash : Hash) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (p : verifier.Prepared)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok p,scratch))
    (parsed : Parsed) (parser : parse (bytesOf proof.val) = some parsed)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    ∃ frame, Read ((eval H prior).1 ++ AuS1_Recovery.log ops B std D pub proof hash input) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (committedRoot parsed 2) ∧
      ∀ q : Fin 22 → Fin 262144, (eval H (SdkC_Replay.replay parsed q)).2 = true →
      let trace := (eval H prior).1 ++ AuS1_Recovery.log ops B std D pub proof hash input
      let Q := firstReads emptyTable trace
      hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred (Q+1040)) emptyTable
        (trace ++ (eval H (SdkC_Replay.replay parsed q)).1) ∨
      ∀ pos, pos < 22 → OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2 (index q 2 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 2 pos) := by
  have wire := (parse_header _ _ parser).2
  obtain ⟨frame,read,target⟩ := AuS1_PrepareRead.frame ops B std D pub proof hash p input scratch success parsed wire
  let trace := (eval H prior).1 ++ AuS1_Recovery.log ops B std D pub proof hash input
  have frameRead : Read trace frame := by
    change frame ∈ ((eval H prior).1 ++ AuS1_Recovery.log ops B std D pub proof hash input).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_right _ read
  have coherent : ∀ a ∈ trace, a.2 = H a.1 := by
    intro a member
    rcases List.mem_append.mp member with before | current
    · exact Op5I_AcceptedCarrierCounterexample.evaluated_reply H prior a before
    · exact AuS1_Recovery.consistent ops B std D hashv source pub proof hash input sha256 H p1 syscall a current
  refine ⟨frame,frameRead,target,?_⟩
  intro q accepted
  exact SdkC_Replay.recover_or_collision H (bytesOf proof.val) parsed parser q accepted trace _
    coherent (Nat.le_refl _) 2 (by decide) frame 3 frameRead target

#print axioms authenticated
end AspisR1.AuS1_Context
end
