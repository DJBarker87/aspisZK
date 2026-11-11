import AspisRec40CallBudget
import AspisOneTxDecision

/-! Instance of the 40-row distinct-read bound at the one-transaction game
agent's terminal decision `AspisOneTx.dV_aspis`, whose all-input budget
(`AspisOneTx.decision_budgetS`, the three merged multiproofs, from
`AspisOneTxMergedBudget.mergedAll_budget`) is 975: the full 40-row experiment
reads at most `Q + 1111` distinct cells (136 transcript + 975 merged slots). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CallBudgetAspis
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment AspisR1

theorem dV_aspis_budget (s : Bytes) : CallBudget.Budget (AspisOneTx.dV_aspis s) 975 :=
  fun H p m => AspisOneTx.decision_budgetS s H p m

theorem projected_first_reads (D : LiteralByteProtocol.Decoder)
    (P : OraclePortStoredExperimentC4.Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).1 ≤
      Q + 1111 :=
  CallBudget.projected_first_reads D AspisOneTx.dV_aspis 975 dV_aspis_budget P Q hq H

theorem verifier_issued (D : LiteralByteProtocol.Decoder) (s : Bytes) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) :
    (eval H (AspisRec40.Decision.verifier D (AspisOneTx.dV_aspis s) pub pf)).1.length ≤ 1111 :=
  CallBudget.verifier_budget D _ 975 (dV_aspis_budget s) H pub pf

#print axioms dV_aspis_budget
#print axioms projected_first_reads
#print axioms verifier_issued

end AspisRec40.CallBudgetAspis
end
