import RPz7_AuS1_PrepareRead
import RPz7_SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Recovery
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.AdaptiveFirstReadLaw
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

 def log (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8)
    (hash : Hash) (input : Array aspis_core.field.wide_exact.WideExact 29#usize) :=
  observe (run (SdkD_PrepareSource.code ops B std D pub proof hash input)).1

 theorem consistent (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (source : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8)
    (hash : Hash) (input : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    ∀ a ∈ log ops B std D pub proof hash input, a.2 = H a.1 := by
  have logs := AuS1_Observe.lower hashv (SdkD_PrepareSource.code ops B std D pub proof hash input)
    (AuS1_Prepare.uniform ops B std D hashv source pub proof hash input) []
  simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at logs
  unfold log
  rw [← logs]
  exact SdkC_Source.consistent hashv sha256 H p1 syscall _

 theorem authenticated (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
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
    ∃ frame, Read (log ops B std D pub proof hash input) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (committedRoot parsed 2) ∧
      ∀ q : Fin 22 → Fin 262144, (eval H (SdkC_Replay.replay parsed q)).2 = true →
      let trace := log ops B std D pub proof hash input
      let Q := firstReads emptyTable trace
      hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred (Q+1040)) emptyTable
        (trace ++ (eval H (SdkC_Replay.replay parsed q)).1) ∨
      ∀ pos, pos < 22 → OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2 (index q 2 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 2 pos) := by
  have wire := (parse_header _ _ parser).2
  obtain ⟨frame,read,target⟩ := AuS1_PrepareRead.frame ops B std D pub proof hash p input scratch success parsed wire
  refine ⟨frame,read,target,?_⟩
  intro q accepted
  exact SdkC_Replay.recover_or_collision H (bytesOf proof.val) parsed parser q accepted
    (log ops B std D pub proof hash input) _
    (consistent ops B std D hashv source pub proof hash input sha256 H p1 syscall)
    (Nat.le_refl _) 2 (by decide) frame 3 read target

#print axioms consistent
#print axioms authenticated
end AspisR1.AuS1_Recovery
end
