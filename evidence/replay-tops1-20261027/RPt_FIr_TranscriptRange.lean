import RPt_FIr_SampleRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_TranscriptRange
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open FIr_SampleRange

theorem program (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (row n : Nat) (P : LiteralTranscript.Prefix) (below : row+n≤25)
    (before : ∀ x∈F3M_ReaderChallenges.ordinaryValues P.rounds,InBase x) :
    ∀ x∈F3M_ReaderChallenges.ordinaryValues
      (eval H (F3J_SamplerRun.program pf row n P)).2.rounds,InBase x := by
  induction n generalizing row P with
  | zero => exact before
  | succ n ih =>
    rw [F3J_SamplerStep.step]
    apply ih (row+1) _ (by omega)
    intro x member
    simp only [F3M_ReaderChallenges.ordinaryValues,FS.Prefix.ext,List.map_append,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member | same
    · exact before x member
    · subst x
      exact sampled H row (by omega) P (pf row)

theorem getD (xs : List LiteralTranscript.E) (all : ∀ x∈xs,InBase x) (j : Nat) :
    InBase (xs.getD j 0) := by
  cases found : xs[j]? with
  | none => simpa only [List.getD,found,Option.getD_none] using FIr_SampleRange.zero
  | some x =>
    have mem : x∈xs := List.mem_of_getElem? found
    simpa only [List.getD,found,Option.getD_some] using all x mem

/-- Challenges in a successful literal view of the actual sampler retain
base-field membership; the rho projection loses no value on semantic rows. -/
theorem view (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (pub : LiteralTranscript.Public) (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (v : LiteralOpeningView.View)
    (read : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix pub))).2))=some v)
    (j : Nat) : InBase ((v.semantic.map Prod.snd).getD j 0) := by
  have values := F3M_OpeningChallenges.values H pf pub 8 p q v read
  rw [values]
  apply getD
  apply program H pf 0 25 (FS.emptyPrefix pub) (by decide)
  intro x mem
  simp only [FS.emptyPrefix,F3M_ReaderChallenges.ordinaryValues,List.map_nil,List.not_mem_nil] at mem

#print axioms program
#print axioms getD
#print axioms view
end AspisR1.FIr_TranscriptRange
end
