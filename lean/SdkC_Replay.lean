import SdkC_GlobalRecovery
import OraclePortFrozen2Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Replay
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

/-- Fixed canonical replay. The source is not changed or charged zero for it. -/
def replay (p : Parsed) (q : Fin 22 → Fin 262144) : Program Bytes State Bool :=
  OraclePortFrozen2.batch p q slots

theorem replay_bound (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    (eval H (replay p q)).1.length ≤ 1040 := by
  have bound := OraclePortFrozen2.batch_bound H p q slots (by
    intro s member
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact bound

theorem firstReads_append_le {I A : Type} [DecidableEq I]
    (table : AspisV8PairedCommitment.Table I A) (left right : List (I × A)) :
    firstReads table (left ++ right) ≤ firstReads table left + right.length := by
  induction left generalizing table with
  | nil => simpa only [List.nil_append,firstReads,Nat.zero_add] using
      VerifierCallBudget.firstReads_le_length table right
  | cons head tail ih =>
    obtain ⟨input,value⟩ := head
    have rest := ih (AspisV8PairedCommitment.put table input value)
    simp only [List.cons_append,firstReads]
    split <;> omega

/-- A response-driven continuation; parsed data and queries come from the
same source output. The experiment is chosen before H. -/
def augmented {A : Type} (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144)) : Program Bytes State A :=
  bind source fun value => bind (replay (prepare value).1 (prepare value).2) fun _ => .done value

theorem augmented_bound {A : Type} (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144)) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    firstReads emptyTable (eval H (augmented source prepare)).1 ≤ Q+1040 := by
  simp only [augmented,eval_bind,eval,List.append_nil]
  exact (firstReads_append_le _ _ _).trans
    (Nat.add_le_add (budget H) (replay_bound H _ _))

/-- ALL extra replay queries are charged in the single collision loss. -/
theorem collision_bound {A : Type} (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144)) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (augmented source prepare) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event
        SelectedTranscriptParams.params.iv (Q+1040) view)) ≤
      6 * ((Q+1040 : Nat) : ℚ)^2 / (256^32 : ℚ) :=
  BinRawByteCollisionTargets.mass SelectedTranscriptParams.params.iv (Q+1040)
    (augmented source prepare) (augmented_bound source prepare Q budget)

/-- Appending replay after an ALREADY READ commitment does not change the
first-commitment extraction prefix. -/
theorem cut_append (log suffix : List (Bytes × State)) (frame : Bytes) (read : Read log frame) :
    BinRawByteCutRecovery.cut (log ++ suffix) frame = BinRawByteCutRecovery.cut log frame := by
  induction log with
  | nil => simp [Read] at read
  | cons head tail ih =>
    obtain ⟨input,value⟩ := head
    by_cases same : input = frame
    · subst frame
      simp [BinRawByteCutRecovery.cut,firstIdx]
    · have rest : Read tail frame := by
        simpa only [Read,List.map_cons,List.mem_cons,same,Ne.symm same,false_or] using read
      simpa only [BinRawByteCutRecovery.cut,List.cons_append,firstIdx,if_neg same,
        List.take_succ_cons] using congrArg (fun xs => (input,value) :: xs) (ih rest)

/-- Indexed recovery from the ORIGINAL source commitment prefix, without a
source-log-containment hypothesis for the canonical replay. Collision is
charged against the augmented log; this is not a source-log equality claim. -/
theorem recover_or_collision (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parser : parse stored = some p) (q : Fin 22 → Fin 262144)
    (accepted : (eval H (replay p q)).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (budget : firstReads emptyTable log ≤ Q)
    (kind : Nat) (hk : kind < 3) (frame : Bytes) (j : Fin 5)
    (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind)) :
    hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1040)) emptyTable (log ++ (eval H (replay p q)).1) ∨
      ∀ pos, pos < 22 → OraclePortAllSelectedRecoveryC6.recovered log frame p kind (index q kind pos) =
        some (OraclePortPackedChoiceC4.payload p kind pos) := by
  classical
  let extended := log ++ (eval H (replay p q)).1
  by_cases collision : hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1040)) emptyTable extended
  · exact Or.inl collision
  right
  have extendedConsistent : ∀ a ∈ extended, a.2 = H a.1 := by
    intro a member
    rcases List.mem_append.mp member with old | fresh
    · exact consistent a old
    · exact Op5I_AcceptedCarrierCounterexample.evaluated_reply H (replay p q) a fresh
  have contains : ∀ a, Read (eval H (replay p q)).1 a → Read extended a := by
    intro a member
    change a ∈ (log ++ (eval H (replay p q)).1).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_right _ member
  have extendedBudget : firstReads emptyTable extended ≤ Q+1040 :=
    (firstReads_append_le _ _ _).trans (Nat.add_le_add budget (replay_bound H p q))
  have extendedFrame : Read extended frame := by
    change frame ∈ (log ++ (eval H (replay p q)).1).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_left _ frameRead
  have recovered := OraclePortFrozenOrder.authenticated H stored p parser q accepted extended (Q+1040)
    extendedConsistent contains extendedBudget collision kind hk frame j extendedFrame rootRead
  intro pos hp
  have result := recovered pos hp
  unfold OraclePortAllSelectedRecoveryC6.recovered at result ⊢
  rw [cut_append log _ frame frameRead] at result
  exact result

#print axioms replay_bound
#print axioms firstReads_append_le
#print axioms augmented_bound
#print axioms collision_bound
#print axioms cut_append
#print axioms recover_or_collision
end AspisR1.SdkC_Replay
end
