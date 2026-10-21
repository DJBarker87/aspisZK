import OraclePortFrozenOrderBounds

/-! All-input budgets at the new fixed decision; no recursive model log
transport. The terminal budget is 1046, verifier 1161, starts Q+1080,
and two-pass recorded log length Q+2322. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrder
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
attribute [local instance] Classical.propDecidable

theorem slots_bound (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat)) :
    (eval H (OraclePortShortCircuit.short (slotPrograms p q ss))).1.length ≤
      (ss.map fun s => 2*(batchPositions s.1).length + capacity (3*s.1+s.2)).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have bound := slot_bound H p q s.1 s.2
    simp only [slotPrograms,List.map_cons,OraclePortShortCircuit.short,eval_bind,
      List.length_append,List.sum_cons]
    cases out : (eval H (verifySlot_frozen p q s.1 s.2)).2
    · simp only [Bool.false_eq_true,if_false,eval,List.length_nil]; omega
    · simp only [if_true]
      change _ + (eval H (OraclePortShortCircuit.short (slotPrograms p q ss))).1.length ≤ _
      omega

theorem decision_budget : Budget dV_frozen := by
  intro stored H tr m
  unfold dV_frozen
  split
  · split
    · rename_i p q hp hq
      have bound := slots_bound H p q slots
      have total : (slots.map fun s => 2*(batchPositions s.1).length +
          capacity (3*s.1+s.2)).sum = 1046 := by rfl
      rw [total] at bound
      simpa only [eval_bind,eval,List.append_nil] using bound
    · simp [eval]
  · simp [eval]

theorem verifier_bound (D : LiteralByteProtocol.Decoder) (i : Input) (H : Bytes → State) :
    (eval H (verifier D dV_frozen i)).1.length ≤ 1161 :=
  verifier_budget D dV_frozen decision_budget H i

theorem distinct_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (annotated D dV_frozen (canon P))).1 ≤ Q+1161 :=
  OraclePortStoredAccountingC4.distinct_bound D dV_frozen (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H) decision_budget H

theorem starts_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D dV_frozen (canon P))).1 ≤ Q+1080 :=
  OraclePortStoredAccountingC4.starts_bound D dV_frozen (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H) decision_budget H

theorem log_length (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    (eval H (annotated D dV_frozen (canon P))).1.length ≤ Q+2322 :=
  recorded_length D dV_frozen (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H) decision_budget H

#print axioms slots_bound
#print axioms decision_budget
#print axioms verifier_bound
#print axioms distinct_bound
#print axioms starts_bound
#print axioms log_length
end AspisR1.OraclePortFrozenOrder
end
