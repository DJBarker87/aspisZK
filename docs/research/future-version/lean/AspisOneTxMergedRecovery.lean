import AspisOneTxMergedSlot
import OraclePortAllSelectedRecoveryC6

/-! The Aspis one-transaction verifier: three-tree recovery of the opened values
at all 22 queried positions from one merged multiproof per tree (item M6 of
ONE-TRANSACTION-GAME.md).

Kind of result: MODEL THEOREM in R1's binary commitment model. Copy of R1's
`OraclePortFrozenOrder.authenticated` (OraclePortFrozenOrderSelectedRecovery.lean),
the theorem R1's bound uses, with: the six short-circuited 10/12-position slots
replaced by three short-circuited 22-position merged slots (`verifyMergedAll`);
`batchOf` removed (every position is in its tree's single slot); R1's `parse`
replaced by `parseSummed`. Conclusion, exceptional event (`AllAddressCollision.bad
iv BinRawByteCollisionTargets.pred Q`), and the objects `recovered`, `payload`,
`index`, `committedRoot` are R1's, unchanged.

NOT established here: that the Rust computes `verifyMergedAll` (source
refinement); the frame/root identification of the 40-row run (`targets`, item M7). -/
set_option autoImplicit false
noncomputable section
namespace AspisOneTx
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.OraclePortCompactDraft AspisR1.OraclePortSelectedDraft AspisR1.OraclePortBatchDraft
open AspisR1.OraclePortAllSelectedRecoveryC6
attribute [local instance] Classical.propDecidable

/-- Copy of R1's `slots_accepted` for any short-circuited list. -/
theorem short_accepted (H : Bytes → State) (ps : List (Program Bytes State Bool))
    (accepted : (eval H (OraclePortShortCircuit.short ps)).2 = true)
    (x : Program Bytes State Bool) (member : x ∈ ps) : (eval H x).2 = true := by
  induction ps with
  | nil => simp at member
  | cons head rest ih =>
    simp only [OraclePortShortCircuit.short,eval_bind] at accepted
    cases first : (eval H head).2
    · simp [first,eval] at accepted
    · simp only [first,if_true] at accepted
      rcases List.mem_cons.mp member with rfl | hm
      · exact first
      · exact ih accepted hm

/-- Copy of R1's `slots_read` for any short-circuited list. -/
theorem short_read (H : Bytes → State) (ps : List (Program Bytes State Bool))
    (accepted : (eval H (OraclePortShortCircuit.short ps)).2 = true)
    (x : Program Bytes State Bool) (member : x ∈ ps)
    (a : Bytes) (read : Read (eval H x).1 a) :
    Read (eval H (OraclePortShortCircuit.short ps)).1 a := by
  induction ps with
  | nil => simp at member
  | cons head rest ih =>
    simp only [OraclePortShortCircuit.short,eval_bind] at accepted ⊢
    cases first : (eval H head).2
    · simp [first,eval] at accepted
    · simp only [first,if_true] at accepted ⊢
      simp only [Read,List.map_append,List.mem_append]
      rcases List.mem_cons.mp member with rfl | hm
      · exact Or.inl read
      · exact Or.inr (ih accepted hm)

theorem merged_member (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) (hk : kind < 3) :
    verifyMerged p q kind ∈ mergedPrograms p q := by
  unfold mergedPrograms
  exact List.mem_map.mpr ⟨kind, by interval_cases kind <;> simp, rfl⟩

/-- Copy of R1's `leaf_fields` for the summed parser. -/
theorem leaf_fields_summed (stored : Bytes) (p : Parsed) (parsed : parseSummed stored = some p)
    (kind pos : Nat) (kindBound : kind < 3) (posBound : pos < 22) :
    leaf p kind pos = BinMerkle32Leaf.leafInput (tag kind)
      (OraclePortPackedChoiceC4.payload p kind pos) (salt p kind pos) ∧
    (OraclePortPackedChoiceC4.payload p kind pos).length = width kind ∧
    (salt p kind pos).length = 32 := by
  obtain ⟨c1,c2,s1,s2,fold,s3⟩ := opening_fields_summed stored p parsed pos posBound
  interval_cases kind
  · exact ⟨rfl,c1,s1⟩
  · exact ⟨rfl,c2,s2⟩
  · exact ⟨rfl,fold,s3⟩

/-- The merged form of R1's `OraclePortFrozenOrder.authenticated`: outside R1's
single collision event, every opened payload of every tree at every queried
position equals the payload recovered from the log cut at that root's
commitment frame. -/
theorem authenticated_merged (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parsed : parseSummed stored = some p) (q : Fin 22 → Fin 262144)
    (accepted : (eval H (verifyMergedAll p q)).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifyMergedAll p q)).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (kind : Nat) (kindBound : kind < 3) (frame : Bytes) (j : Fin 5)
    (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind)) :
    ∀ pos, pos < 22 → recovered log frame p kind (index q kind pos) =
      some (OraclePortPackedChoiceC4.payload p kind pos) := by
  intro pos posBound
  have member := merged_member p q kind kindBound
  have slotOK := short_accepted H _ accepted _ member
  have slotReads := fun a ha => short_read H _ accepted _ member a ha
  obtain ⟨leafBytes,packedWidth,saltWidth⟩ := leaf_fields_summed stored p parsed kind pos kindBound posBound
  have recoveredAt := merged_recovery_at_index H p q kind pos posBound slotOK log Q consistent
    (fun a ha => contains a (slotReads a ha)) bound clean frame j frameRead rootRead (tag kind) (width kind)
    (OraclePortPackedChoiceC4.payload p kind pos) (salt p kind pos) leafBytes packedWidth saltWidth
  unfold recovered
  rw [recoveredAt]
  rfl

/-- What an attack after ρ would need, refuted in the slot model: two accepted
merged multiproof runs over the same parsed root and log bind the same payload
at a common queried index (both equal the recovered value). -/
theorem no_second_opening_merged (H : Bytes → State) (stored stored' : Bytes) (p p' : Parsed)
    (parsed : parseSummed stored = some p) (parsed' : parseSummed stored' = some p')
    (q q' : Fin 22 → Fin 262144)
    (accepted : (eval H (verifyMergedAll p q)).2 = true)
    (accepted' : (eval H (verifyMergedAll p' q')).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifyMergedAll p q)).1 a → Read log a)
    (contains' : ∀ a, Read (eval H (verifyMergedAll p' q')).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (kind : Nat) (kindBound : kind < 3) (frame : Bytes) (j : Fin 5)
    (frameRead : Read log frame)
    (sameRoot : committedRoot p' kind = committedRoot p kind)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind))
    (pos pos' : Nat) (posBound : pos < 22) (posBound' : pos' < 22)
    (sameIndex : index q' kind pos' = index q kind pos) :
    OraclePortPackedChoiceC4.payload p' kind pos' = OraclePortPackedChoiceC4.payload p kind pos := by
  have a := authenticated_merged H stored p parsed q accepted log Q consistent contains bound clean
    kind kindBound frame j frameRead rootRead pos posBound
  have b := authenticated_merged H stored' p' parsed' q' accepted' log Q consistent contains' bound clean
    kind kindBound frame j frameRead (by rw [sameRoot]; exact rootRead) pos' posBound'
  unfold recovered at a b
  rw [sameIndex, sameRoot] at b
  rw [a] at b
  exact (Option.some.inj b).symm

#print axioms short_accepted
#print axioms short_read
#print axioms leaf_fields_summed
#print axioms authenticated_merged
#print axioms no_second_opening_merged
end AspisOneTx
end
