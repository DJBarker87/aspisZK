import OraclePortFrozenOrderCutRecovery
import OraclePortAllSelectedRecoveryC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrder
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortAllSelectedRecoveryC6
attribute [local instance] Classical.propDecidable

theorem slots_accepted (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat))
    (accepted : (eval H (OraclePortShortCircuit.short (slotPrograms p q ss))).2 = true)
    (bk : Nat × Nat) (member : bk ∈ ss) :
    (eval H (verifySlot_frozen p q bk.1 bk.2)).2 = true := by
  induction ss with
  | nil => simp at member
  | cons head rest ih =>
    simp only [slotPrograms,List.map_cons,OraclePortShortCircuit.short,eval_bind] at accepted
    cases first : (eval H (verifySlot_frozen p q head.1 head.2)).2
    · simp [first,eval] at accepted
    · simp only [first,if_true] at accepted
      rcases List.mem_cons.mp member with rfl | hm
      · exact first
      · exact ih accepted hm

theorem slots_read (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat))
    (accepted : (eval H (OraclePortShortCircuit.short (slotPrograms p q ss))).2 = true)
    (bk : Nat × Nat) (member : bk ∈ ss)
    (a : Bytes) (read : Read (eval H (verifySlot_frozen p q bk.1 bk.2)).1 a) :
    Read (eval H (OraclePortShortCircuit.short (slotPrograms p q ss))).1 a := by
  induction ss with
  | nil => simp at member
  | cons head rest ih =>
    simp only [slotPrograms,List.map_cons,OraclePortShortCircuit.short,eval_bind] at accepted ⊢
    cases first : (eval H (verifySlot_frozen p q head.1 head.2)).2
    · simp [first,eval] at accepted
    · simp only [first,if_true] at accepted ⊢
      simp only [Read,List.map_append,List.mem_append]
      rcases List.mem_cons.mp member with rfl | hm
      · exact Or.inl read
      · exact Or.inr (ih accepted hm)

theorem authenticated (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parsed : parse stored = some p) (q : Fin 22 → Fin 262144)
    (accepted : (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (kind : Nat) (kindBound : kind < 3) (frame : Bytes) (j : Fin 5)
    (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind)) :
    ∀ pos, pos < 22 → recovered log frame p kind (index q kind pos) =
      some (OraclePortPackedChoiceC4.payload p kind pos) := by
  intro pos posBound
  have member := slot_member pos kind kindBound
  have slotOK := slots_accepted H p q slots accepted (batchOf pos,kind) member
  have slotReads := slots_read H p q slots accepted (batchOf pos,kind) member
  obtain ⟨leafBytes,packedWidth,saltWidth⟩ := leaf_fields stored p parsed kind pos kindBound posBound
  have recoveredAt := recovery_at_index H p q (batchOf pos) kind pos
    (batch_member pos posBound) slotOK log Q consistent (fun a ha => contains a (slotReads a ha))
    bound clean frame j frameRead rootRead (tag kind) (width kind)
    (OraclePortPackedChoiceC4.payload p kind pos) (salt p kind pos) leafBytes packedWidth saltWidth
  unfold recovered
  rw [recoveredAt]
  rfl

#print axioms slots_accepted
#print axioms slots_read
#print axioms authenticated
end AspisR1.OraclePortFrozenOrder
end
