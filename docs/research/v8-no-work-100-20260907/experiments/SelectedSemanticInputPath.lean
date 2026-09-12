import SelectedSemanticAfterstateChecksV2
import SelectedMembershipDecode

/-!
The actual 72 constant-weight selected membership links and Boolean row
positions32..48 construct all eight PathResiduals fields on the SAME early
C1 table. The 24 levels are one input-pair level, twenty lane levels and
three forest levels. The existing V7-backed selected path/decoder theorem
then identifies the selected note, its same-key nullifier and public anchor.

RowsVanish, mathematical Poseidon gates and the alias branch remain explicit.
No verifier acceptance, authenticated historical checkpoint, collision-free
hashing, early-family membership or successful extraction is inferred.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.SelectedSemanticInputPath
open scoped BigOperators
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7FixedWidth29TupleList
open AspisV8.SelectedWeightedCopyCore AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedCopyAliases AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedEarlyC1Inputs
open AspisV8.SelectedEarlyC1Outputs AspisV8.SelectedEarlyC1InputPair
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedSemanticAfterstateChecks
noncomputable section

def pathLink (level : Fin 24) (edge : Fin 3) : Fin 136 :=
  ⟨64 + 3 * level.val + edge.val, by omega⟩
def sourceRow (level : Fin 24) (edge : Fin 3) : Nat :=
  if edge.val = 0 then SelectedForestPath.boundaryRow level.val
  else SelectedForestPath.auxRow level.val + 1
def targetRow (level : Fin 24) (edge : Fin 3) : Nat :=
  if edge.val = 0 then SelectedForestPath.auxRow level.val
  else if edge.val = 1 then 16 * SelectedForestPath.nodeBlock level.val + 12
  else 16 * SelectedForestPath.nodeBlock level.val
def sourceStart (edge : Fin 3) : Nat := if edge.val = 2 then 8 else 0
def targetStart (edge : Fin 3) : Nat :=
  if edge.val = 0 then 1 else if edge.val = 1 then 0 else 8
def targetOffset (edge : Fin 3) : Nat := if edge.val = 2 then 1051521018 else 0

set_option maxRecDepth 1000 in
/-- Only the72 literal registry cells and their short tuple patterns are
reduced here. No table, challenge field or recurrence occurs. -/
theorem path_link_shape (level : Fin 24) (edge : Fin 3) :
    selectedKind (pathLink level edge) = .one ∧
    (producer (pathLink level edge)).row.val = sourceRow level edge ∧
    (consumer (pathLink level edge)).row.val = targetRow level edge ∧
    sourcePatterns (producer (pathLink level edge)).pattern =
      ⟨8, sourceStart edge, 0⟩ ∧
    sourcePatterns (consumer (pathLink level edge)).pattern =
      ⟨8, targetStart edge, targetOffset edge⟩ := by
  fin_cases level <;> fin_cases edge <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- First derive weight=1 and an equality in QM31, then project its base
coordinate. Inactive slots elsewhere and all copy pole conditions are not
erased by this argument. -/
theorem path_copy_limb (candidate : C1InitialMessages) (index : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer index)
    (level : Fin 24) (edge : Fin 3) (limb : Fin 8) :
    semanticTable candidate (sourceRow level edge) (sourceStart edge + limb.val) =
      semanticTable candidate (targetRow level edge) (targetStart edge + limb.val) +
        if limb.val = 7 then (targetOffset edge : F) else 0 := by
  obtain ⟨kind, source, target, sourcePattern, targetPattern⟩ := path_link_shape level edge
  have weight : selectedWeight (K := QM31Exact) .transfer index (pathLink level edge) = 1 := by
    simp only [selectedWeight, kind, publicWeight, weightBit, if_true]
  let lane : Fin 16 := ⟨limb.val, by omega⟩
  have sourceLive : lane.val < (sourcePatterns (producer (pathLink level edge)).pattern).width := by
    rw [sourcePattern]
    exact limb.isLt
  have targetLive : lane.val < (sourcePatterns (consumer (pathLink level edge)).pattern).width := by
    rw [targetPattern]
    exact limb.isLt
  have equal := aliases (pathLink level edge) lane
  rw [weight, one_mul] at equal
  have projected := congrArg (fun value : QM31Exact => value.re.re) (sub_eq_zero.mp equal)
  rw [project_pattern_limb candidate _ lane sourceLive,
    project_pattern_limb candidate _ lane targetLive, sourcePattern, targetPattern,
    source, target] at projected
  have last : lane.val + 1 = 8 ↔ limb.val = 7 := by dsimp only [lane]; omega
  simpa only [lane, last, Nat.cast_zero, ite_self, add_zero] using projected

theorem path_copies (candidate : C1InitialMessages) (index : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer index) :
    (∀ (level : Fin 24) (limb : Fin 8),
      SelectedForestPath.boundary (semanticTable candidate) level.val limb -
        SelectedForestPath.current (semanticTable candidate) level.val limb = 0) ∧
    (∀ (level : Fin 24) (limb : Fin 8),
      SelectedForestPath.left (semanticTable candidate) level.val limb -
        SelectedForestPath.nodeLeft (semanticTable candidate) level.val limb = 0) ∧
    (∀ (level : Fin 24) (limb : Fin 8),
      SelectedForestPath.right (semanticTable candidate) level.val limb -
        SelectedForestPath.nodeRight (semanticTable candidate) level.val limb = 0) := by
  have offset : (1051521018 : F) = -NODE_TWEAK :=
    eq_neg_iff_add_eq_zero.mpr literal_right_offset_cancels
  refine ⟨?_, ?_, ?_⟩
  · intro level limb
    apply sub_eq_zero.mpr
    simpa [sourceRow, targetRow, sourceStart, targetStart, targetOffset,
      SelectedForestPath.boundary, SelectedForestPath.current, SelectedForestPath.digest]
      using path_copy_limb candidate index aliases level 0 limb
  · intro level limb
    apply sub_eq_zero.mpr
    simpa [sourceRow, targetRow, sourceStart, targetStart, targetOffset,
      SelectedForestPath.left, SelectedForestPath.nodeLeft, SelectedForestPath.digest]
      using path_copy_limb candidate index aliases level 1 limb
  · intro level limb
    apply sub_eq_zero.mpr
    have copied := path_copy_limb candidate index aliases level 2 limb
    by_cases last : limb.val = 7
    · simpa [sourceRow, targetRow, sourceStart, targetStart, targetOffset,
        SelectedForestPath.right, SelectedForestPath.nodeRight,
        SelectedForestPath.digest, offset, last, sub_eq_add_neg] using copied
    · simpa [sourceRow, targetRow, sourceStart, targetStart, targetOffset,
        SelectedForestPath.right, SelectedForestPath.nodeRight,
        SelectedForestPath.digest, offset, last, sub_eq_add_neg] using copied

theorem path_mask_at (level : Fin 24) :
    pathMask (SelectedForestPath.auxRow level.val) ∧
      SelectedForestPath.auxRow level.val < 1024 := by
  have bounds := SelectedForestPath.exact_decoder_coordinates level
  have modulo : SelectedForestPath.auxRow level.val % 4 = 1 := by
    unfold SelectedForestPath.auxRow
    omega
  exact ⟨⟨bounds.2.1, by omega, modulo⟩, by omega⟩

theorem path_selection (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    (∀ level : Fin 24, t (SelectedForestPath.auxRow level.val) 0 *
      (t (SelectedForestPath.auxRow level.val) 0 - 1) = 0) ∧
    (∀ (level : Fin 24) (limb : Fin 8),
      (1-t (SelectedForestPath.auxRow level.val) 0) *
        (SelectedForestPath.left t level.val limb-SelectedForestPath.current t level.val limb)=0) ∧
    (∀ (level : Fin 24) (limb : Fin 8),
      t (SelectedForestPath.auxRow level.val) 0 *
        (SelectedForestPath.right t level.val limb-SelectedForestPath.current t level.val limb)=0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro level
    have zero := zero_at pub t vanish .direction _ (path_mask_at level).2
    simpa [SelectedSemanticRows.residual, directionResidual, gate, (path_mask_at level).1]
      using zero
  · intro level limb
    have zero := zero_at pub t vanish (.left limb) _ (path_mask_at level).2
    simpa [SelectedSemanticRows.residual, leftResidual, gate, (path_mask_at level).1,
      SelectedForestPath.left, SelectedForestPath.current, SelectedForestPath.digest] using zero
  · intro level limb
    have zero := zero_at pub t vanish (.right limb) _ (path_mask_at level).2
    simpa [SelectedSemanticRows.residual, rightResidual, gate, (path_mask_at level).1,
      SelectedForestPath.right, SelectedForestPath.current, SelectedForestPath.digest] using zero

theorem path_initial_low (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t)
    (level : Fin 24) (limb : Fin 8) :
    t (16 * SelectedForestPath.nodeBlock level.val) limb.val = 0 := by
  let block := SelectedForestPath.nodeBlock level.val
  have bound : block < 57 := by
    dsimp only [block, SelectedForestPath.nodeBlock]
    split <;> omega
  have node : SelectedSemanticRows.nodeBlock block := by
    dsimp only [block, SelectedForestPath.nodeBlock, SelectedSemanticRows.nodeBlock]
    split <;> omega
  have notFirst : ¬firstBlock block := by
    dsimp only [block, SelectedForestPath.nodeBlock, firstBlock]
    split <;> omega
  let column : Fin 16 := ⟨limb.val, by omega⟩
  have low : column.val < 8 := limb.isLt
  have modulo : (16*block) % 16 = 0 := by omega
  have quotient : (16*block) / 16 = block := by omega
  have notInput : 16*block ≠ 1017 := by omega
  have notOutput : 16*block ≠ 1018 := by omega
  have zero := zero_at pub t vanish (.initial column) (16*block) (by omega)
  simpa [SelectedSemanticRows.residual, initialResidual, modulo, quotient,
    notFirst, node, low, occupancyResidual, gate, notInput, notOutput, column] using zero

/-- The path model and the all57-block Poseidon premise use the SAME
absorbed state and rows, including the initial rate8 absorption. -/
theorem path_pair_state (t : BaseTable) (level pair : Nat) :
    SelectedForestPath.pairState t level pair =
      SelectedNoteRecovery.pairState t (SelectedForestPath.nodeBlock level) pair := by
  cases pair with
  | zero =>
    funext limb
    by_cases low : limb.val < 8 <;>
      simp [SelectedForestPath.pairState, SelectedForestPath.absorbed,
        SelectedNoteRecovery.pairState, SelectedNoteRecovery.absorbed,
        SelectedNoteRecovery.state, SelectedNoteRecovery.chunk, absorb, low]
  | succ pair => rfl

theorem path_residuals (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    SelectedForestPath.PathResiduals rc (semanticTable candidate) := by
  have copies := path_copies candidate pub.appendIndex aliases
  have selection := path_selection pub (semanticTable candidate) vanish
  refine ⟨selection.1, selection.2.1, selection.2.2, copies.1, copies.2.1,
    copies.2.2, path_initial_low pub (semanticTable candidate) vanish, ?_⟩
  intro level pair limb
  rw [path_pair_state, path_pair_state]
  have bound : SelectedForestPath.nodeBlock level.val < 57 := by
    unfold SelectedForestPath.nodeBlock
    split <;> omega
  exact poseidon ⟨SelectedForestPath.nodeBlock level.val, bound⟩ pair limb

/-- The literal anchor summand is isolated, retaining the entire dynamic
append digest expression. No append index bound or caller check is needed. -/
theorem digest_at_anchor (pub : Public) (t : BaseTable) (limb : Fin 8) :
    digestResidual pub t 907 limb = t 907 limb.val - pub.anchor limb := by
  have notCarry (within : SelectedAppendAfterstate.carryIndex pub.appendIndex < 20) :
      907 ≠ 16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11 := by omega
  unfold digestResidual appendDigestResidual
  rw [sibling_sum_at_eleven pub t 907 (by decide) limb]
  by_cases within : SelectedAppendAfterstate.carryIndex pub.appendIndex < 20
  · simp [gate, dif_pos within, notCarry within]
  · simp [gate, dif_neg within]

theorem anchor_binding (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t)
    (limb : Fin 8) : t 907 limb.val - pub.anchor limb = 0 := by
  have zero := zero_at pub t vanish (.digest limb) 907 (by decide)
  change digestResidual pub t 907 limb = 0 at zero
  rw [digest_at_anchor] at zero
  exact zero

/-- Construct the canonical raw table and reuse the selected 24-level
decoder/forest proof. This connects the actual selected pair commitment,
owner/key/note/nullifier and anchor, not an arbitrary supplied witness. -/
theorem same_table_input_membership (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    (SelectedPairDecoder.inputPair (semanticTable candidate)).selectedCommitment
        (SelectedMembershipDecode.rawDirection (rawSemanticTable candidate) 0) =
      noteHash rc (ownerHash rc (SelectedNoteRecovery.key (semanticTable candidate)))
        (semanticTable candidate 44 0) pub.asset
        (SelectedNoteRecovery.salt (semanticTable candidate)) ∧
    pub.nullifier = nullifierHash rc (SelectedNoteRecovery.key (semanticTable candidate))
      (SelectedNoteRecovery.salt (semanticTable candidate)) ∧
    SelectedMembershipDecode.decodedForestRoot rc (rawSemanticTable candidate) = pub.anchor := by
  have rawPath : SelectedForestPath.PathResiduals rc
      (SelectedOutputNotes.rawTable (rawSemanticTable candidate)) := by
    rw [rawTable_exact]
    exact path_residuals rc pub candidate vanish poseidon aliases
  have rawNotes : SelectedNoteRecovery.NoteResiduals rc
      (SelectedOutputNotes.rawTable (rawSemanticTable candidate)) := by
    rw [rawTable_exact]
    exact input_residuals_from_selected_copy rc candidate pub.appendIndex
      (note_checks rc pub candidate vanish poseidon).1 aliases
  have fields := public_checks pub (semanticTable candidate) vanish
  have rawCell (row column : Nat) :
      (rawSemanticTable candidate row column : F) = semanticTable candidate row column :=
    ZMod.natCast_zmod_val _
  have result := SelectedMembershipDecode.same_decoded_note_nullifier_and_anchor rc
    (rawSemanticTable candidate) (fun row _ column _ => raw_canonical candidate row column)
    rawPath rawNotes pub.asset pub.nullifier pub.anchor
    (by rw [rawCell]; exact fields.1)
    (by intro limb; rw [rawCell]; exact fields.2.1 limb)
    (by intro limb; rw [rawCell]; exact anchor_binding pub _ vanish limb)
  simpa only [rawTable_exact, rawCell] using result

#print axioms path_link_shape
#print axioms path_copy_limb
#print axioms path_copies
#print axioms path_mask_at
#print axioms path_selection
#print axioms path_initial_low
#print axioms path_pair_state
#print axioms path_residuals
#print axioms digest_at_anchor
#print axioms anchor_binding
#print axioms same_table_input_membership
end
end AspisV8.SelectedSemanticInputPath
