import AspisRec40CleanA
import AspisOneTxChecks

/-! Aspis 40-row clean event: `clean40`, R1's `Frozen2StartChargeClean.clean`
for the 40-row experiment at the one-transaction decision `dV_aspis`.

Two named hypotheses, with exactly the shapes stated in
`AspisRec40CleanStatement` / RECORDED-EXPERIMENT-40.md §7.2:
* `hchecks`: `CheckedAcceptance40` at every stored input (the game agent's
  M9; R1's `fibre_checks`). It is stated at `ChargePrefix.prover P`, which is
  R1's `pairProver s P` as a program (R1's `Frozen2StartChargePrefix.fibre_prover`).
* `hfinal`: decoding of rows 33 to 39 on the charged run, under R1's four
  premises of `Frozen2StartChargeCompletion.decodes` (mine, to be discharged).
Everything else is proved here: the full experiment equals the recorded
decision experiment, acceptance and output transport, the constructor
schedule and `Format` from `AspisChecks` fields, the public tag from
`admitted_aspis`/`accepted_guardS`, the word alignment, and the assembly. -/
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
