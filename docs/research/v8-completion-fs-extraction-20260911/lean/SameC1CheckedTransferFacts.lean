import SelectedSemanticInputPath

/-! One selected early-C1 table constructs both the transfer/afterstate facts
and the input ownership/membership facts. This is a deterministic semantic
endpoint, not proof-acceptance enforcement, an executable permitted-access
extractor, caller authentication or literal Rust validator refinement.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
namespace AspisV8.SameC1CheckedTransferFacts
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisPool.V7FixedWidth29TupleList
open AspisV8.SelectedCopyAliases AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedSemanticOutputTransition AspisV8.SelectedSemanticAfterstateChecks
open AspisV8.SelectedSemanticInputPath
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedEarlyC1InputPair
open AspisV8.SelectedEarlyC1Outputs
open AspisV8.SelectedPairDecoder AspisV8.SelectedMembershipDecode
noncomputable section

/-- The field-stage pair parser uses the SAME canonical raw side as the
membership path. All24 raw bit reads parse, and the stored UInt32 lane index
has exactly the next20 bits. No independently supplied decoded index or
successful raw parser is assumed. -/
def RawInputDecoderFacts (candidate : C1InitialMessages) : Prop :=
  decodeInputPairFields (semanticTable candidate) =
      some (inputPair (semanticTable candidate),
        rawDirection (rawSemanticTable candidate) 0) ∧
    (∀ level : Fin 24, parseRawDirection (rawSemanticTable candidate) level.val =
      some (rawDirection (rawSemanticTable candidate) level.val)) ∧
    (laneIndex (rawSemanticTable candidate)).toNat < 2^20 ∧
    (∀ i : Nat, i < 20 →
      (laneIndex (rawSemanticTable candidate)).toNat.testBit i =
        rawDirection (rawSemanticTable candidate) (i+1)) ∧
    (∀ i : Nat, 20 ≤ i →
      (laneIndex (rawSemanticTable candidate)).toNat.testBit i = false)

theorem selected_residuals_construct_raw_input_decoder
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    RawInputDecoderFacts candidate := by
  have rawPath : SelectedForestPath.PathResiduals rc
      (SelectedOutputNotes.rawTable (rawSemanticTable candidate)) := by
    rw [rawTable_exact]
    exact path_residuals rc pub candidate vanish poseidon aliases
  have rawPair : InputPairResiduals
      (SelectedOutputNotes.rawTable (rawSemanticTable candidate)) NODE_TWEAK := by
    rw [rawTable_exact]
    exact input_pair_residuals_from_selected_copy candidate pub.appendIndex
      (pair_checks pub candidate vanish) aliases
  have canonical : ∀ row, row < 1024 → ∀ column, column < 16 →
      rawSemanticTable candidate row column < p :=
    fun row _ column _ => raw_canonical candidate row column
  have decoded := same_raw_input_pair_checked rc (rawSemanticTable candidate)
    canonical rawPath rawPair
  refine ⟨?_, ?_, decoded_lane_index_contract (rawSemanticTable candidate)⟩
  · simpa only [rawTable_exact] using decoded
  · intro level
    exact all_raw_directions_parse rc (rawSemanticTable candidate) canonical rawPath level

/-- No valid-witness or decoder-success hypothesis: the exact selected
semantic, Poseidon and copy residuals, public transition comparisons and
explicit carry correspondence construct all conclusions for the same table.
The comparisons do not authenticate their public source or caller. -/
theorem selected_residuals_construct_transfer_and_membership
    (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (sequence nextIndex rustCarry : Nat)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex)
    (comparisons : SourceComparisons pub sequence nextIndex rustCarry)
    (carryExact : rustCarry = SelectedAppendAfterstate.carryIndex pub.appendIndex) :
    TransferTransitionFacts rc pub candidate sequence nextIndex ∧
    ((SelectedPairDecoder.inputPair (semanticTable candidate)).selectedCommitment
        (rawDirection (rawSemanticTable candidate) 0) =
      noteHash rc (ownerHash rc (AspisV8.SelectedNoteRecovery.key (semanticTable candidate)))
        (semanticTable candidate 44 0) pub.asset
        (AspisV8.SelectedNoteRecovery.salt (semanticTable candidate))) ∧
    pub.nullifier = nullifierHash rc
      (AspisV8.SelectedNoteRecovery.key (semanticTable candidate))
      (AspisV8.SelectedNoteRecovery.salt (semanticTable candidate)) ∧
    decodedForestRoot rc (rawSemanticTable candidate) = pub.anchor ∧
    RawInputDecoderFacts candidate := by
  have transition := SelectedSemanticAfterstateChecks.semantic_transfer_transition
    rc pub candidate sequence nextIndex rustCarry vanish poseidon aliases comparisons carryExact
  have membership := same_table_input_membership rc pub candidate vanish poseidon aliases
  have decoded := selected_residuals_construct_raw_input_decoder
    rc pub candidate vanish poseidon aliases
  exact ⟨transition, membership.1, membership.2.1, membership.2.2, decoded⟩

#print selected_residuals_construct_transfer_and_membership
#print axioms selected_residuals_construct_raw_input_decoder
#print axioms selected_residuals_construct_transfer_and_membership
end
end AspisV8.SameC1CheckedTransferFacts
