import AspisFormal.Pool.V7PairLeafOccupancy

/-! Source-shaped fallible input-pair decoding from selected forest C1.
The occupancy digest is NOT the digest read by the witness decoder. Two
actual copy links through the pair hash's right input connect them below.
The field-level checker starts after canonical M31 decoding. No theorem here
assumes successful decoding, pair validity, an honest trace or a payment witness.
Hash/path-root correctness and probabilistic constraint enforcement are separate.
-/
set_option autoImplicit false
namespace AspisV8.SelectedPairDecoder
open AspisPool.V7PairLeafOccupancy
variable {K : Type} [Field K] [DecidableEq K]
abbrev Table (K : Type*) := Nat → Nat → K

def pathRow (level : Fin 24) : Nat := 913 + 16*(level.val/4) + 4*(level.val%4)
def readDigest (t : Table K) (row start : Nat) : Digest K :=
  fun i => t row (start+i.val)
def inputPair (t : Table K) : PairLeaf K where
  firstCommitment := readDigest t 914 0
  secondCommitment := readDigest t 914 8
  secondOccupied := t 1017 0
  secondOccupancyInverse := t 1017 1

/-- Both selected copy links use this same right-input tweak convention.
The pinned Rust value is1095962629; its value cancels from the alias proof. -/
def nodeRight (t : Table K) (tweak : K) (i : Fin 8) : K :=
  t 64 (8+i.val) + if i.val = 7 then -tweak else 0

structure InputPairResiduals (t : Table K) (tweak : K) : Prop where
  directionBoolean : ∀ level,
    t (pathRow level) 0 * (t (pathRow level) 0 - 1) = 0
  occupiedBoolean : t 1017 0 * (t 1017 0 - 1) = 0
  sentinelInverse : t 1017 9 * t 1017 1 - t 1017 0 = 0
  emptyInverse : (1-t 1017 0)*t 1017 1 = 0
  emptyDigest : ∀ i : Fin 8, (1-t 1017 0)*t 1017 (2+i.val) = 0
  selectedSpend : t 1017 10 * (1-t 1017 0) = 0
  selectedCopy : t 913 0 - t 1017 10 = 0
  pathRightCopy : ∀ i : Fin 8, t 914 (8+i.val) - nodeRight t tweak i = 0
  occupancyRightCopy : ∀ i : Fin 8, nodeRight t tweak i - t 1017 (2+i.val) = 0

omit [DecidableEq K] in
/-- This is the nontrivial source handoff: the decoder's second commitment
equals the occupancy-certificate digest, without assuming either is valid. -/
theorem decoder_digest_is_occupancy_digest (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) :
    (inputPair t).secondCommitment = readDigest t 1017 2 := by
  funext i
  exact (sub_eq_zero.mp (h.pathRightCopy i)).trans
    (sub_eq_zero.mp (h.occupancyRightCopy i))

omit [DecidableEq K] in
theorem decoded_pair_valid (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) : (inputPair t).Valid := by
  have aliases := decoder_digest_is_occupancy_digest t tweak h
  refine ⟨h.occupiedBoolean, ?_, h.emptyInverse, ?_⟩
  · change (inputPair t).secondCommitment ⟨7, by decide⟩ * _ = _
    rw [aliases]
    exact sub_eq_zero.mp h.sentinelInverse
  · intro i
    change (1-t 1017 0)*(inputPair t).secondCommitment i = 0
    rw [aliases]
    exact h.emptyDigest i

/-- Literal field-stage branch order of recovered_witness::bit. -/
def decodeSide (bit : K) : Option Bool :=
  if bit = 0 then some false else if bit = 1 then some true else none
def selectedSide (bit : K) : Bool := decide (bit = 1)

theorem side_decoder_of_boolean (bit : K) (boolean : bit*(bit-1)=0) :
    decodeSide bit = some (selectedSide bit) := by
  rcases mul_eq_zero.mp boolean with zero | one
  · simp [decodeSide, selectedSide, zero]
  · have h : bit = 1 := sub_eq_zero.mp one
    simp [decodeSide, selectedSide, h]

theorem all_twenty_four_directions_decode (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) :
    ∀ level, decodeSide (t (pathRow level) 0) =
      some (selectedSide (t (pathRow level) 0)) := by
  intro level
  exact side_decoder_of_boolean _ (h.directionBoolean level)

theorem decoded_selected_slot_spendable (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) :
    (inputPair t).SelectedSlotIsSpendable (selectedSide (t 913 0)) := by
  by_cases selected : t 913 0 = 1
  · have copied : t 1017 10 = 1 :=
      (sub_eq_zero.mp h.selectedCopy).symm.trans selected
    have occupied : t 1017 0 = 1 := by
      have gate := h.selectedSpend
      rw [copied, one_mul] at gate
      exact (sub_eq_zero.mp gate).symm
    simpa [selectedSide, selected, PairLeaf.SelectedSlotIsSpendable,
      PairLeaf.selectedOccupied, inputPair] using occupied
  · simp [selectedSide, selected, PairLeaf.SelectedSlotIsSpendable,
      PairLeaf.selectedOccupied]

/-- Field portion of PairLeaf::validate, including its final defensive
occupied-sentinel test. Canonical raw-byte rejection precedes this model. -/
def validatePairFields (leaf : PairLeaf K) : Option Unit :=
  if leaf.secondOccupied*(leaf.secondOccupied-1) ≠ 0 then none
  else if leaf.secondSentinel*leaf.secondOccupancyInverse ≠ leaf.secondOccupied then none
  else if (1-leaf.secondOccupied)*leaf.secondOccupancyInverse ≠ 0 then none
  else if ∃ i, (1-leaf.secondOccupied)*leaf.secondCommitment i ≠ 0 then none
  else if leaf.secondOccupied = 1 ∧ leaf.secondSentinel = 0 then none
  else some ()

/-- Reuses V7's algebraic nonzero-sentinel theorem to discharge the final
source check; it is not assumed from honest salt generation. -/
theorem v7_valid_implies_field_validator (leaf : PairLeaf K) (valid : leaf.Valid) :
    validatePairFields leaf = some () := by
  have noBadLimb : ¬ ∃ i, (1-leaf.secondOccupied)*leaf.secondCommitment i ≠ 0 := by
    intro ⟨i, bad⟩
    exact bad (valid.2.2.2 i)
  have sentinel : ¬ (leaf.secondOccupied = 1 ∧ leaf.secondSentinel = 0) := by
    intro ⟨occupied, zero⟩
    exact valid_occupied_second_sentinel_ne_zero leaf valid occupied zero
  rw [validatePairFields, if_neg (not_not_intro valid.1),
    if_neg (not_not_intro valid.2.1), if_neg (not_not_intro valid.2.2.1),
    if_neg noBadLimb, if_neg sentinel]

def decodeInputPairFields (t : Table K) : Option (PairLeaf K × Bool) := do
  let side ← decodeSide (t 913 0)
  let _ ← validatePairFields (inputPair t)
  if side && decide ((inputPair t).secondOccupied ≠ 1) then none
  else some (inputPair t, side)

/-- A checked input-pair and the literal private side are returned from the
selected cells. The exact source residuals, not `Valid`/decoder success, are
the assumptions of this endpoint. All24 separate path directions also parse. -/
theorem residuals_imply_checked_input_decode (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) :
    decodeInputPairFields t = some (inputPair t, selectedSide (t 913 0)) ∧
      (inputPair t).Valid ∧
      (inputPair t).SelectedSlotIsSpendable (selectedSide (t 913 0)) ∧
      (∀ level, decodeSide (t (pathRow level) 0) =
        some (selectedSide (t (pathRow level) 0))) := by
  have valid := decoded_pair_valid t tweak h
  have checked := v7_valid_implies_field_validator (inputPair t) valid
  have spendable := decoded_selected_slot_spendable t tweak h
  have parsed := all_twenty_four_directions_decode t tweak h
  refine ⟨?_, valid, spendable, parsed⟩
  have first := parsed 0
  change decodeSide (t 913 0) = some (selectedSide (t 913 0)) at first
  by_cases side : selectedSide (t 913 0) = true
  · have occupied : (inputPair t).secondOccupied = 1 := by
      simpa [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied, side] using spendable
    simp [decodeInputPairFields, first, checked, occupied]
  · have sideFalse : selectedSide (t 913 0) = false := Bool.eq_false_iff.mpr side
    simp [decodeInputPairFields, first, checked, sideFalse]

theorem occupied_decoded_slot_has_nonzero_sentinel (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) (selected : selectedSide (t 913 0) = true) :
    (inputPair t).secondSentinel ≠ 0 := by
  have valid := decoded_pair_valid t tweak h
  have spent := decoded_selected_slot_spendable t tweak h
  have occupied : (inputPair t).secondOccupied = 1 := by
    simpa [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied, selected] using spent
  exact valid_occupied_second_sentinel_ne_zero (inputPair t) valid occupied

/-- The first side is occupied independently of the second side's sentinel.
Zero coordinates are legal; no nonzero-digest/preimage assumption is added. -/
theorem empty_second_is_exact (t : Table K) (tweak : K)
    (h : InputPairResiduals t tweak) (empty : t 1017 0 = 0) :
    (inputPair t).secondCommitment = (fun _ => 0) ∧ t 1017 1 = 0 := by
  have valid := decoded_pair_valid t tweak h
  exact ⟨valid_empty_second_commitment_zero (inputPair t) valid empty,
    valid_empty_second_inverse_zero (inputPair t) valid empty⟩

theorem selected_path_cells_pinned :
    pathRow 0 = 913 ∧ pathRow 1 = 917 ∧ pathRow 20 = 993 ∧
      pathRow 21 = 997 ∧ pathRow 22 = 1001 ∧ pathRow 23 = 1005 := by decide

theorem all_selected_path_reads_in_shape (level : Fin 24) :
    912 ≤ pathRow level ∧ pathRow level + 1 < 1008 := by
  unfold pathRow
  omega

#print axioms decoder_digest_is_occupancy_digest
#print axioms decoded_pair_valid
#print axioms all_twenty_four_directions_decode
#print axioms decoded_selected_slot_spendable
#print axioms v7_valid_implies_field_validator
#print axioms residuals_imply_checked_input_decode
#print axioms occupied_decoded_slot_has_nonzero_sentinel
#print axioms empty_second_is_exact
#print axioms selected_path_cells_pinned
#print axioms all_selected_path_reads_in_shape
end AspisV8.SelectedPairDecoder
