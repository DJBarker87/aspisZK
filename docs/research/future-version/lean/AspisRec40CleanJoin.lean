import AspisRec40Clean
import AspisOneTxCheckedAcceptance
import AspisFailureBound

/-! Aspis 40-row clean event, join with the one-transaction game agent's
`fibre_checks40` and the assembly's three open hypotheses (option (a) of the
coordinator's message: the three definitions of `AspisFailureBound` proved as
stated).

* `checks_of_fibre`: R1's selection step for 40 rows. The game agent's
  `AspisOneTx.Checked.fibre_checks40` is stated at R1's `pairProver s P`;
  R1's `Frozen2StartChargePrefix.fibre_prover` (`pairProver s P = prover P`)
  carries it to `ChargePrefix.prover P`, and `AspisRec40.CleanA.projected_eq_recorded`
  (the full experiment at the stored input of the run equals the recorded
  decision experiment at `d (stored)`) lifts the fixed-proof statement to the
  full experiment inside `accepted_facts`.
* `accepted_checks40`, `word_alignment40`: `AspisFailureBound.AcceptedChecks40`
  and `WordAlignment40`, unconditionally (R1's query hypothesis only).
* `hit_in_prefix40`: `AspisFailureBound.HitInPrefix40`, conditional on
  `hfinal` (decoding of rows 33 to 39 on the charged run, R1's four premises). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanJoin
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 RawRecordedOracleExtractionMassBin
attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad
  AspisAcceptance.bad AspisOneTx.dV_aspis

theorem checks_of_fibre (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (s : Bytes) :
    AspisRec40.CleanStatement.CheckedAcceptance40 D (AspisOneTx.dV_aspis s)
      (AspisRec40.ChargePrefix.prover P) (Q+1111) := by
  have h := AspisOneTx.Checked.fibre_checks40 D s P Q hq
  rw [Frozen2StartChargePrefix.fibre_prover] at h
  exact h

theorem accepted_checks40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    AspisFailureBound.AcceptedChecks40 D P Q := by
  intro H ha hc
  obtain ⟨c, _, _⟩ := AspisRec40.Clean.accepted_facts D P Q (checks_of_fibre D P Q hq) H hc ha
  exact ⟨c⟩

theorem word_alignment40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    AspisFailureBound.WordAlignment40 D P Q := by
  intro H ha hc
  obtain ⟨_, fixed, _⟩ := AspisRec40.Clean.accepted_facts D P Q (checks_of_fibre D P Q hq) H hc ha
  exact fixed

theorem hit_in_prefix40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hfinal : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 →
      ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
          BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
          (eval H (AspisRec40.ChargePrefix.base D P)).1 →
      RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 →
      AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
      AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P))) :
    AspisFailureBound.HitInPrefix40 D P Q := by
  intro H ha hc hit
  exact AspisRec40.Clean.hit_in_prefix_of D P Q hq (checks_of_fibre D P Q hq) hfinal H ha hc hit

#print axioms checks_of_fibre
#print axioms accepted_checks40
#print axioms word_alignment40
#print axioms hit_in_prefix40

end AspisRec40.CleanJoin
end
