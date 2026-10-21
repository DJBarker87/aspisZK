import OraclePortIndexedRecoveryC4
import OraclePortPackedChoiceC4
import OraclePortStoredWidthsC4

/-! All 22 positions are recovered at their exact indices, including the
10/12 split and duplicates. Commitment-frame provenance and the containing
execution are explicit, rather than assuming a globally equal recovered map. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAllSelectedRecoveryC6
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
attribute [local instance] Classical.propDecidable

def batchOf (pos : Nat) : Nat := if pos < 10 then 0 else 1

def tag (kind : Nat) : BinMerkle32Path.Byte := if kind = 0 then 0x71 else if kind = 1 then 0xf1 else 0x72

def width (kind : Nat) : Nat := if kind = 0 then 480 else 128

def salt (p : Parsed) (kind pos : Nat) : Bytes :=
  slice (opening p pos) (if kind = 0 then 608 else if kind = 1 then 640 else 800) 32

def recovered (log : List (Bytes × State)) (frame : Bytes) (p : Parsed) (kind i : Nat) : Option Bytes :=
  (BinRawByteCutStability.recoverAt (tag kind) (width kind)
    (BinRawByteCutRecovery.cut log frame) (BinMultiproof.slots 18 i) (committedRoot p kind)).map Prod.fst

theorem batch_member (pos : Nat) (bound : pos < 22) : pos ∈ batchPositions (batchOf pos) := by
  by_cases early : pos < 10
  · simp only [batchOf,if_pos early,batchPositions,ite_true,List.mem_range]; exact early
  · simp only [batchOf,if_neg early,batchPositions,show (1:Nat) ≠ 0 by decide,ite_false]
    exact List.mem_map.mpr ⟨pos-10,List.mem_range.mpr (by omega),by omega⟩

theorem slot_member (pos kind : Nat) (bound : kind < 3) : (batchOf pos,kind) ∈ slots := by
  unfold batchOf
  split <;> interval_cases kind <;> decide

theorem leaf_fields (stored : Bytes) (p : Parsed) (parsed : parse stored = some p)
    (kind pos : Nat) (kindBound : kind < 3) (posBound : pos < 22) :
    leaf p kind pos = BinMerkle32Leaf.leafInput (tag kind)
      (OraclePortPackedChoiceC4.payload p kind pos) (salt p kind pos) ∧
    (OraclePortPackedChoiceC4.payload p kind pos).length = width kind ∧
    (salt p kind pos).length = 32 := by
  obtain ⟨c1,c2,s1,s2,fold,s3⟩ := OraclePortStoredWidthsC4.opening_fields stored p parsed pos posBound
  interval_cases kind
  · exact ⟨rfl,c1,s1⟩
  · exact ⟨rfl,c2,s2⟩
  · exact ⟨rfl,fold,s3⟩

/-- Indexed opening recovery for every position in the accepted stored batch. -/
theorem authenticated (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parsed : parse stored = some p) (q : Fin 22 → Fin 262144)
    (accepted : (eval H (verifySlots p q slots)).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifySlots p q slots)).1 a → Read log a)
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
  have slotOK := OraclePortStoredLeafRecoveryC4.slots_accepted H p q slots accepted (batchOf pos,kind) member
  have slotReads := OraclePortStoredLeafRecoveryC4.slots_read H p q slots (batchOf pos,kind) member
  obtain ⟨leafBytes,packedWidth,saltWidth⟩ := leaf_fields stored p parsed kind pos kindBound posBound
  have recoveredAt := OraclePortIndexedRecoveryC4.recovery_at_index H p q (batchOf pos) kind pos
    (batch_member pos posBound) slotOK log Q consistent (fun a ha => contains a (slotReads a ha))
    bound clean frame j frameRead rootRead (tag kind) (width kind)
    (OraclePortPackedChoiceC4.payload p kind pos) (salt p kind pos) leafBytes packedWidth saltWidth
  unfold recovered
  rw [recoveredAt]
  rfl

#print axioms batch_member
#print axioms slot_member
#print axioms leaf_fields
#print axioms authenticated
end AspisR1.OraclePortAllSelectedRecoveryC6
end
