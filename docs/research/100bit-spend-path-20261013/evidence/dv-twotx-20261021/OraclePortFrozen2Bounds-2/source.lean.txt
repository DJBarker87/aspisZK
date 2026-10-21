import OraclePortFrozen2Decision
import OraclePortFrozen2Resource

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozen2
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft OraclePortFrozenOrder
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
attribute [local instance] Classical.propDecidable

theorem batch_bound (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat)) (positive : ∀ s ∈ ss, 0 < capacity (3*s.1+s.2)) :
    (eval H (batch p q ss)).1.length ≤
      (ss.map fun s => 2*(batchPositions s.1).length + capacity (3*s.1+s.2) - 1).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have bound := OraclePortFrozen2Resource.slot H p q s.1 s.2 (positive s (by simp))
    have rest := ih (fun t ht => positive t (by simp [ht]))
    simp only [batch,slotPrograms,List.map_cons,OraclePortShortCircuit.short,eval_bind,
      List.length_append,List.sum_cons]
    cases out : (eval H (verifySlot_frozen p q s.1 s.2)).2
    · simp only [Bool.false_eq_true,if_false,eval,List.length_nil]; omega
    · simp only [if_true]
      change _ + (eval H (batch p q ss)).1.length ≤ _
      omega

theorem batch0_bound (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    (eval H (batch p q batch0)).1.length ≤ 477 := by
  have h := batch_bound H p q batch0 (by
    intro s hs
    simp only [batch0,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide)
  exact h

theorem batch1_bound (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    (eval H (batch p q batch1)).1.length ≤ 563 := by
  have h := batch_bound H p q batch1 (by
    intro s hs
    simp only [batch1,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide)
  exact h

theorem after_bound (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix) :
    (eval H (afterBatch0 stored p q tr)).1.length ≤ 569 := by
  unfold afterBatch0
  split
  · rename_i i v hi hv
    simp only [eval_bind,checkpoint_value,stage2,eval_bind,eval,List.append_nil,List.length_append]
    have hc := checkpoint_reads H stored p q tr i v
    have hb := batch1_bound H p q
    omega
  · simp [eval]

theorem decision_budget : Budget dV_frozen2 := by
  intro stored H tr m
  unfold dV_frozen2
  split
  · split
    · rename_i p q hp hq
      have before := batch0_bound H p q
      have after := after_bound H stored p q tr
      simp only [eval_bind,List.length_append]
      cases hb : (eval H (batch p q batch0)).2 <;> simp only [if_true,Bool.false_eq_true,if_false,eval,List.length_nil] <;> omega
    · simp [eval]
  · simp [eval]

theorem verifier_bound (D : LiteralByteProtocol.Decoder) (i : Input) (H : Bytes → State) :
    (eval H (verifier D dV_frozen2 i)).1.length ≤ 1161 :=
  verifier_budget D dV_frozen2 decision_budget H i

theorem distinct_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (annotated D dV_frozen2 (canon P))).1 ≤ Q+1161 :=
  OraclePortStoredAccountingC4.distinct_bound D dV_frozen2 (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H) decision_budget H

theorem log_length (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    (eval H (annotated D dV_frozen2 (canon P))).1.length ≤ Q+2322 :=
  recorded_length D dV_frozen2 (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H) decision_budget H

#print axioms batch_bound
#print axioms batch0_bound
#print axioms batch1_bound
#print axioms after_bound
#print axioms decision_budget
#print axioms verifier_bound
#print axioms distinct_bound
#print axioms log_length
end AspisR1.OraclePortFrozen2
end
