import AspisRec40CleanA
import AspisOneTxChecks
import AspisLib_Tag

/-! Aspis 40-row clean event, the statement tag: `accepted_tag` (with
`guard_tag`, `tag_of_admitS`), the public tag of an accepted run is 2.
It uses the Aspis admission (`admitS`, through `admitted_aspis` and
`accepted_guardS`) and keeps only the tag conjunct of the guard, on the
first 33 rounds. It uses no validity of rows 33 to 39. It is one of the
pieces `AspisRec40Clean.accepted_facts` assembles. Model level. (An earlier
header here was a copy of `AspisRec40Clean`'s.) -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanTag
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RawCutProverCompiler (experiment)
open CanonicalCutEnrichedTranscript (Words enrichMessage)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-! ## Public tag, from the admission of `dV_aspis` -/

attribute [local irreducible] AspisOneTx.dV_aspis

/-- The guard's first conjunct, for an arbitrary erased prefix (kept abstract so
that no projection of a concrete transcript is ever reduced). -/
theorem guard_tag (X : RawCutTranscriptRun.ErasedPrefix)
    (h : OraclePortAdmission.Guard (AspisOneTx.take33 X)) : X.statement.tag = 2 := h.1

/-- The tag from any admitted decision (`admitS core`). Only the statement's tag
is read (the guard's first conjunct, on the first 33 rounds); nothing about rows
33 to 39 is taken from admission. -/
theorem tag_of_admitS (D : LiteralByteProtocol.Decoder) (core : OraclePortExperiment.Decision)
    (P : RawCutProverCompiler.Prover) (H : Bytes → State)
    (ha : (eval H (AspisRec40.Decision.original D (AspisOneTx.admitS core) P)).2.2 = true) :
    (eval H P).2.1.tag = 2 := by
  rw [AspisRec40.CleanA.original_accepts] at ha
  unfold OracleDecisionFeasibilityCore.onBytes at ha
  have hg := guard_tag _ (AspisOneTx.accepted_guardS core H _ _ ha).1
  rw [AspisRows40.Protocol.transcript_eq, InitialTagDecision.erased_transcript_tag] at hg
  exact hg

theorem accepted_tag (D : LiteralByteProtocol.Decoder) (s : Bytes)
    (P : RawCutProverCompiler.Prover) (H : Bytes → State)
    (ha : (eval H (AspisRec40.Decision.original D (AspisOneTx.dV_aspis s) P)).2.2 = true) :
    (eval H P).2.1.tag = 2 := by
  have ha' : (eval H (AspisRec40.Decision.original D
      (AspisOneTx.admitS (AspisOneTx.dV_aspis s)) P)).2.2 = true := by
    rw [AspisOneTx.admitted_aspis]; exact ha
  exact tag_of_admitS D _ P H ha'

#print axioms guard_tag
#print axioms tag_of_admitS
#print axioms accepted_tag

end AspisRec40.CleanTag
end
