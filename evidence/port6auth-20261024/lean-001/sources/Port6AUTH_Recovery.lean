import Port4B_CallerJoin
import OraclePortFrozenOrderSelectedRecovery
import Port5Q1_Parsed
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Recovery
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortAllSelectedRecoveryC6

/-- Recovery from the two actual batch logs, without assuming a global verifier
join. The frame is an actual read of this same containing execution. -/
theorem batches (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parsed : parse stored=some p) (q : Fin 22 → Fin 262144)
    (log0 log1 log : List (Bytes × State)) (Q : Nat)
    (batch0 : eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)=(log0,true))
    (batch1 : eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)=(log1,true))
    (contains0 : ∀ a, Read log0 a → Read log a)
    (contains1 : ∀ a, Read log1 a → Read log a)
    (consistent : ∀ a ∈ log, a.2=H a.1)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (kind : Nat) (kindBound : kind<3) (frame : Bytes) (j : Fin 5)
    (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame=some (committedRoot p kind)) :
    ∀ pos, pos<22 → recovered log frame p kind (index q kind pos)=
      some (OraclePortPackedChoiceC4.payload p kind pos) := by
  intro pos hp
  have bm := batch_member pos hp
  have sm : (batchOf pos,kind) ∈
      (if pos<10 then OraclePortFrozen2.batch0 else OraclePortFrozen2.batch1) := by
    unfold batchOf
    split <;> interval_cases kind <;> decide
  have ba : (eval H (OraclePortFrozen2.batch p q
      (if pos<10 then OraclePortFrozen2.batch0 else OraclePortFrozen2.batch1))).2=true := by
    split <;> simp only [batch0,batch1]
  have slot := OraclePortFrozenOrder.slots_accepted H p q _ ba _ sm
  have reads := OraclePortFrozenOrder.slots_read H p q _ ba _ sm
  have containing : ∀ a, Read (eval H (OraclePortFrozenOrder.verifySlot_frozen p q (batchOf pos) kind)).1 a → Read log a := by
    intro a ha
    have r := reads a ha
    by_cases early : pos<10
    · simp only [if_pos early,batch0] at r
      exact contains0 a r
    · simp only [if_neg early,batch1] at r
      exact contains1 a r
  obtain ⟨lf,pw,sw⟩ := leaf_fields stored p parsed kind pos kindBound hp
  have result := OraclePortFrozenOrder.recovery_at_index H p q (batchOf pos) kind pos bm slot
    log Q consistent containing bound clean frame j frameRead rootRead (tag kind) (width kind)
    (OraclePortPackedChoiceC4.payload p kind pos) (salt p kind pos) lf pw sw
  unfold recovered
  rw [result]
  rfl

/-- Repeated parents agree because BOTH source openings recover at the SAME
indexed cut. No equal-root shortcut or arbitrary map-equality premise. -/
theorem repeated (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parsed : parse stored=some p) (q : Fin 22 → Fin 262144)
    (log0 log1 log : List (Bytes × State)) (Q : Nat)
    (batch0 : eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)=(log0,true))
    (batch1 : eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)=(log1,true))
    (contains0 : ∀ a, Read log0 a → Read log a)
    (contains1 : ∀ a, Read log1 a → Read log a)
    (consistent : ∀ a ∈ log, a.2=H a.1)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (frame : Bytes) (j : Fin 5) (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame=some (committedRoot p 2))
    (a b : Fin 22) (same : index q 2 a.val=index q 2 b.val) :
    OraclePortPackedChoiceC4.payload p 2 a.val=OraclePortPackedChoiceC4.payload p 2 b.val := by
  have auth := batches H stored p parsed q log0 log1 log Q batch0 batch1 contains0 contains1
    consistent bound clean 2 (by decide) frame j frameRead rootRead
  have ha := auth a.val a.isLt
  rw [same,auth b.val b.isLt] at ha
  exact (Option.some.inj ha).symm

#print axioms batches
#print axioms repeated
end AspisR1.Port6AUTH_Recovery
end
