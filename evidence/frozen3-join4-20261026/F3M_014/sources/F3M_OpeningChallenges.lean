import F3M_OpeningReader
import F3M_ChallengeTransport
import F3M_SamplerPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_OpeningChallenges
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

theorem values (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (pub : LiteralTranscript.Public) (tail : Nat) (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (v : LiteralOpeningView.View)
    (read : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 0 (25+tail) (FS.emptyPrefix pub))).2))=some v) :
    v.semantic.map Prod.snd=F3M_ReaderChallenges.ordinaryValues
      (eval H (F3J_SamplerRun.program pf 0 25 (FS.emptyPrefix pub))).2.rounds := by
  let P := (eval H (F3J_SamplerRun.program pf 0 25 (FS.emptyPrefix pub))).2
  let Q := (eval H (F3J_SamplerRun.program pf 0 (25+tail) (FS.emptyPrefix pub))).2
  have length : P.rounds.length=25 := F3J_SamplerRun.length H pf 0 25 (FS.emptyPrefix pub)
  have retained : Q.rounds.take 25=P.rounds := by
    dsimp only [Q]
    rw [F3J_SamplerCompose.value]
    exact length ▸ F3M_SamplerPrefix.retained H pf 25 tail P
  have projection := F3M_ReaderChallenges.values 0 _ _ (F3M_OpeningReader.components _ v read).1
  calc
    _ = (F3M_ReaderChallenges.ordinaryValues (OraclePortStoredDecisionDraftC4.typedRows p q
        (LiteralTranscript.erasePrefix Q))).take 25 := by
      simpa only [F3M_ReaderChallenges.ordinaryValues,List.map_take] using projection
    _ = (F3M_ReaderChallenges.ordinaryValues Q.rounds).take 25 := by
      rw [F3M_ChallengeTransport.restored]
    _ = F3M_ReaderChallenges.ordinaryValues (Q.rounds.take 25) := by
      simp only [F3M_ReaderChallenges.ordinaryValues,List.map_take]
    _ = _ := congrArg F3M_ReaderChallenges.ordinaryValues retained

#print axioms values
end AspisR1.F3M_OpeningChallenges
end
