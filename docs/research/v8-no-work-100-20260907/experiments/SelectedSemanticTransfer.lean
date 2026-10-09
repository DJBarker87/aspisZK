import SelectedSemanticRowsV3
import SelectedEarlyC1PaymentFacts

/-! The exact same transfer95 Boolean semantic oracle discharges the
selected amount, initial/padding, occupancy/direction, and public binding
premises. Actual Poseidon round-pair equations and one early-family copy
collision alternative remain explicit. The conclusion is TransferFacts,
NOT a full checked-transfer witness, verifier acceptance, membership proof,
append afterstate, or caller/account authority.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedSemanticTransfer
open scoped BigOperators
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7ExtractedLaneWords AspisPool.V7FixedWidth29TupleList
open AspisPool.V7C1SubfieldRecovery
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedPaymentRecovery AspisV8.SelectedAmountEndpoint
open AspisV8.SelectedTransferPositive
open AspisV8.SelectedNoteRecovery AspisV8.SelectedOutputNotes
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedEarlyC1Inputs
open AspisV8.SelectedEarlyC1Outputs AspisV8.SelectedEarlyC1InputPair
open AspisV8.SelectedEarlyC1PaymentFacts
open AspisV8.EarlyC1CopyCollision AspisV8.SelectedCopyAliases
open AspisV8.SelectedCopyAliasQM31 AspisV8.PositivePackBinding
noncomputable section

theorem zero_at (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t)
    (coordinate : Coordinate) (row : Nat) (bounded : row < 1024) :
    residual pub t coordinate row = 0 :=
  coordinate_zero pub t vanish coordinate ⟨row, bounded⟩

theorem tenAt_eq_sum (t : BaseTable) (row : Nat) :
    tenAt t row = ∑ bit : Fin 10, t row bit.val * (2 : F)^bit.val := by
  rw [tenAt, sourceHorner_sum]
  have combined : (∑ i ∈ Finset.range 9, t row i * (2 : F)^i) +
      t row 9 * (2 : F)^9 = ∑ i ∈ Finset.range 10, t row i * (2 : F)^i :=
    (Finset.sum_range_succ (fun i => t row i * (2 : F)^i) 9).symm
  rw [combined, Finset.sum_range]

theorem bit_limb_view (t : BaseTable) (which : Fin 3) (view : Fin 3) (bit : Fin 10) :
    bitValue t which (limbBit view bit) = t (viewRow (valueBase which) view) bit.val := by
  fin_cases view
  · simp [bitValue, bitCell, limbBit, viewRow, bit.isLt, Nat.mod_eq_of_lt bit.isLt]
  · have lower : ¬10 + bit.val < 10 := by omega
    have upper : 10 + bit.val < 20 := by omega
    have modulo : (10 + bit.val) % 10 = bit.val := by omega
    simp [bitValue, bitCell, limbBit, viewRow, lower, upper, modulo]
  · have lower : ¬20 + bit.val < 10 := by omega
    have upper : ¬20 + bit.val < 20 := by omega
    have modulo : (20 + bit.val) % 10 = bit.val := by omega
    simp [bitValue, bitCell, limbBit, viewRow, lower, upper, modulo]

theorem reconstruction_same (t : BaseTable) (which : Fin 3) :
    reconstructAt t (valueBase which) = compiledReconstruction t which := by
  unfold reconstructAt compiledReconstruction
  apply Finset.sum_congr rfl
  intro view _
  rw [tenAt_eq_sum, sourceBlock_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro bit _
  rw [bit_limb_view]

theorem amount_checks (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    AmountSemanticChecks t := by
  have selected (which : Fin 3) : valueMask (valueBase which) := by
    fin_cases which <;> simp [valueMask, valueBase]
  have bounded (which : Fin 3) : valueBase which < 1024 := by unfold valueBase; omega
  constructor
  · intro which bit
    have zero := zero_at pub t vanish (.rangeBit bit) _ (bounded which)
    simpa only [residual, gate, if_pos (selected which), bitAt, bitValue, bitCell] using zero
  · intro which
    have zero := zero_at pub t vanish .recomposition _ (bounded which)
    simpa only [residual, gate, if_pos (selected which), reconstruction_same] using zero
  · intro which
    have next := zero_at pub t vanish .auxiliaryNext _ (bounded which)
    have xor := zero_at pub t vanish .auxiliaryXor _ (bounded which)
    exact ⟨by simpa only [residual, gate, if_pos (selected which)] using next,
      by simpa only [residual, gate, if_pos (selected which)] using xor⟩
  · simpa [residual, gate] using
      zero_at pub t vanish (.conservation ⟨0, by decide⟩) 1014 (by decide)
  · simpa [residual, gate] using
      zero_at pub t vanish (.conservation ⟨1, by decide⟩) 1014 (by decide)

theorem positive_check (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    ProductInverseResidual t := by
  simpa [residual, gate, ProductInverseResidual] using
    zero_at pub t vanish .positive 1014 (by decide)

/-- The complete selected initial states now use the actual moved rows;
the old V7 row704/736 initial checks are not reused as correspondences. -/
theorem initial_checks (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    (∀ i : Fin 16, t 0 i.val - initState DOM_OWNER 8 i = 0) ∧
    (∀ i : Fin 16, t 16 i.val - initState DOM_NOTE 18 i = 0) ∧
    (∀ i : Fin 16, t 400 i.val - initState DOM_NULLIFIER 16 i = 0) ∧
    (∀ which : Fin 2, ∀ i : Fin 16,
      t (16 * outputBlock which) i.val - initState DOM_NOTE 18 i = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa [residual, SelectedSemanticRows.initialResidual, gate, firstBlock,
      SelectedSemanticRows.nodeBlock, firstDomain, firstLength, occupancyResidual] using
      zero_at pub t vanish (.initial i) 0 (by decide)
  · intro i
    simpa [residual, SelectedSemanticRows.initialResidual, gate, firstBlock,
      SelectedSemanticRows.nodeBlock, firstDomain, firstLength, occupancyResidual] using
      zero_at pub t vanish (.initial i) 16 (by decide)
  · intro i
    simpa [residual, SelectedSemanticRows.initialResidual, gate, firstBlock,
      SelectedSemanticRows.nodeBlock, firstDomain, firstLength, occupancyResidual] using
      zero_at pub t vanish (.initial i) 400 (by decide)
  · intro which i
    fin_cases which
    · simpa [residual, SelectedSemanticRows.initialResidual, gate, firstBlock,
        SelectedSemanticRows.nodeBlock, firstDomain, firstLength, occupancyResidual,
        outputBlock] using zero_at pub t vanish (.initial i) 432 (by decide)
    · simpa [residual, SelectedSemanticRows.initialResidual, gate, firstBlock,
        SelectedSemanticRows.nodeBlock, firstDomain, firstLength, occupancyResidual,
        outputBlock] using zero_at pub t vanish (.initial i) 480 (by decide)

theorem note_tail_checks (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    (∀ i : Fin 6, t 60 (i.val + 2) = 0) ∧
    (∀ which : Fin 2, ∀ i : Fin 6,
      t (16 * (outputBlock which + 2) + 12) (i.val + 2) = 0) := by
  have atTail (row : Nat) (tail : row = 60 ∨ row = 476 ∨ row = 524) (i : Fin 6) :
      t row (i.val + 2) = 0 := by
    let column : Fin 16 := ⟨i.val + 2, by omega⟩
    have lower : 2 ≤ column.val := by dsimp only [column]; omega
    have upper : column.val < 8 := by dsimp only [column]; omega
    have notHigh : ¬8 ≤ column.val := by omega
    have zero := zero_at pub t vanish (.absorption column) row (by omega)
    rcases tail with rfl | rfl | rfl <;>
      simpa [residual, SelectedSemanticRows.absorptionResidual, gate, chunkTwo,
        chunkEight, SelectedSemanticRows.nodeBlock, lower, upper, notHigh, column] using zero
  refine ⟨fun i => atTail 60 (Or.inl rfl) i, ?_⟩
  intro which i
  fin_cases which
  · simpa [outputBlock] using atTail 476 (Or.inr (Or.inl rfl)) i
  · simpa [outputBlock] using atTail 524 (Or.inr (Or.inr rfl)) i

theorem pair_checks (pub : Public) (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate)) : InputPairSemanticChecks candidate := by
  let t := semanticTable candidate
  constructor
  · intro level
    have active : pathMask (SelectedPairDecoder.pathRow level) := by
      unfold pathMask SelectedPairDecoder.pathRow
      omega
    have zero := zero_at pub t vanish .direction (SelectedPairDecoder.pathRow level)
      (by have := SelectedPairDecoder.all_selected_path_reads_in_shape level; omega)
    simpa only [residual, directionResidual, gate, if_pos active] using zero
  · simpa [residual, SelectedSemanticRows.initialResidual, gate, occupancyResidual] using
      zero_at pub t vanish (.initial ⟨0, by decide⟩) 1017 (by decide)
  · simpa [residual, SelectedSemanticRows.initialResidual, gate, occupancyResidual] using
      zero_at pub t vanish (.initial ⟨1, by decide⟩) 1017 (by decide)
  · simpa [residual, SelectedSemanticRows.initialResidual, gate, occupancyResidual] using
      zero_at pub t vanish (.initial ⟨2, by decide⟩) 1017 (by decide)
  · intro i
    let column : Fin 16 := ⟨3 + i.val, by omega⟩
    have not0 : column.val ≠ 0 := by dsimp only [column]; omega
    have not1 : column.val ≠ 1 := by dsimp only [column]; omega
    have not2 : column.val ≠ 2 := by dsimp only [column]; omega
    have small : column.val < 11 := by dsimp only [column]; omega
    have index : column.val - 1 = 2 + i.val := by dsimp only [column]; omega
    simpa [residual, SelectedSemanticRows.initialResidual, gate, occupancyResidual,
      not0, not1, not2, small, index] using
      zero_at pub t vanish (.initial column) 1017 (by decide)
  · simpa [residual, SelectedSemanticRows.initialResidual, gate, occupancyResidual] using
      zero_at pub t vanish (.initial ⟨11, by decide⟩) 1017 (by decide)

theorem append_digest_below (pub : Public) (t : BaseTable) (row : Nat)
    (below : row < 539) (limb : Fin 8) : appendDigestResidual pub t row limb = 0 := by
  have empty : ∀ level : Fin 20, row ≠ 16 * (34 + level.val) := by intro level; omega
  have live : ∀ level : Fin 20, row ≠ 16 * (34 + level.val) + 12 := by intro level; omega
  have carry : row ≠ 16 * (33 + SelectedAppendAfterstate.carryIndex pub.appendIndex) + 11 := by
    omega
  have root : row ≠ 859 := by omega
  have sumZero : (∑ level : Fin 20,
      if pub.appendIndex.testBit level.val then
        gate (row = 16 * (34 + level.val) + 12) (t row limb.val - pub.frontier level limb)
      else gate (row = 16 * (34 + level.val))
        (t row (8 + limb.val) - (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro level _
    split <;> simp only [gate, if_neg (empty level), if_neg (live level)]
  simp only [appendDigestResidual, sumZero, gate, if_neg root, zero_add]
  split <;> simp only [if_neg carry]

theorem public_checks (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    (t 44 1 - pub.asset = 0) ∧
    (∀ i : Fin 8, t 427 i.val - pub.nullifier i = 0) ∧
    (∀ which : Fin 2, t (amountRow (outputBlock which)) 1 - pub.asset = 0) ∧
    (∀ which : Fin 2, ∀ i : Fin 8,
      t (16 * (outputBlock which + 2) + 11) i.val - pub.commitments which i = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [residual, scalarResidual, gate] using
      zero_at pub t vanish (.scalar ⟨0, by decide⟩) 44 (by decide)
  · intro i
    simpa [residual, digestResidual, gate, append_digest_below pub t 427 (by decide) i] using
      zero_at pub t vanish (.digest i) 427 (by decide)
  · intro which
    fin_cases which
    · simpa [residual, scalarResidual, gate, outputBlock, amountRow] using
        zero_at pub t vanish (.scalar ⟨1, by decide⟩) 460 (by decide)
    · simpa [residual, scalarResidual, gate, outputBlock, amountRow] using
        zero_at pub t vanish (.scalar ⟨1, by decide⟩) 508 (by decide)
  · intro which i
    fin_cases which
    · simpa [residual, digestResidual, gate, outputBlock,
        append_digest_below pub t 475 (by decide) i] using
        zero_at pub t vanish (.digest i) 475 (by decide)
    · simpa [residual, digestResidual, gate, outputBlock,
        append_digest_below pub t 523 (by decide) i] using
        zero_at pub t vanish (.digest i) 523 (by decide)

/-- Separate actual mathematical two-round gates for all57 selected blocks.
No equality of an arbitrary supplied Poseidon oracle to these gates is assumed. -/
def PoseidonChecks (rc : RoundConstants) (t : BaseTable) : Prop :=
  ∀ block : Fin 57, BlockResiduals rc t block.val

theorem note_checks (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate)) :
    InputSemanticChecks rc candidate ∧ OutputSemanticChecks rc candidate := by
  have initial := initial_checks pub (semanticTable candidate) vanish
  have padding := note_tail_checks pub (semanticTable candidate) vanish
  constructor
  · refine ⟨?_, initial.1, initial.2.1, initial.2.2.1, padding.1⟩
    intro block active
    have bounded : block < 57 := by simp only [activeBlocks, Finset.mem_insert,
      Finset.mem_singleton] at active; omega
    exact poseidon ⟨block, bounded⟩
  · refine ⟨?_, initial.2.2.2, padding.2⟩
    intro which j
    have bounded : outputBlock which + j.val < 57 := by
      fin_cases which <;> simp only [outputBlock, Matrix.cons_val_zero,
        Matrix.cons_val_succ] <;> omega
    exact poseidon ⟨outputBlock which + j.val, bounded⟩

/-- Genuine deterministic residual-to-decoder implication. The positivity
residual is derived from sourceposition94, rather than supplied as successful
decoding or a tablePositivePack hypothesis. One alias family serves all facts. -/
theorem transfer_facts (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    TransferFacts rc candidate pub.asset pub.nullifier pub.commitments := by
  let t := semanticTable candidate
  have amount := amount_checks pub t vanish
  have compiled : CompiledAmountResiduals t :=
    ⟨amount.boolean, amount.recomposition, amount.auxiliary,
      weighted_aliases_supply_amount_aliases candidate pub.appendIndex aliases,
      amount.first, amount.second⟩
  have amounts : AmountFacts t := selected_strict_amounts t
    (compiled_value_residuals t compiled) (compiled_conservation_residuals t compiled)
    (positive_check pub t vanish)
  have notes := note_checks rc pub candidate vanish poseidon
  have fields := public_checks pub t vanish
  refine ⟨amounts, ?_, ?_, ?_⟩
  · exact public_input_facts_of_aliases rc candidate pub.appendIndex notes.1 aliases
      pub.asset pub.nullifier fields.1 fields.2.1
  · exact input_pair_facts_of_aliases candidate pub.appendIndex
      (pair_checks pub candidate vanish) aliases
  · exact output_facts_of_aliases rc candidate pub.appendIndex amounts notes.2 aliases
      pub.asset pub.commitments fields.2.2.1 fields.2.2.2

/-- The pre-lambda family/copy conditions are not consequences of the
semantic oracle. The conclusion keeps the one actual sequential copy collision
alternative and does not identify post-challenge reconstruction with a member. -/
theorem member_transfer_or_copy_collision
    (rc : RoundConstants) (pub : Public) (c1 : C1InitialWords) (candidate : C1InitialMessages)
    (member : candidate ∈ EarlyC1Family.family c1)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions candidate .transfer pub.appendIndex lambda chi helper)
    (packedZero : ∀ row group, packedRows pub (semanticTable candidate) row group = 0)
    (poseidon : PoseidonChecks rc (semanticTable candidate)) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable candidate row.val column.val) = memberTable candidate row column.val) ∧
    (TransferFacts rc candidate pub.asset pub.nullifier pub.commitments ∨
      (lambda, chi) ∈ collisionPairs c1 .transfer pub.appendIndex lambdas chis) := by
  refine ⟨semanticTable_embeds c1 candidate member baseWord, ?_⟩
  rcases source_member_covered c1 .transfer pub.appendIndex lambdas chis lambda chi
      lambdaMember chiMember candidate member helper copy with aliases | collision
  · exact Or.inl (transfer_facts rc pub candidate ((packedRows_zero_iff pub _).mp packedZero)
      poseidon aliases)
  · exact Or.inr collision

#print axioms zero_at
#print axioms tenAt_eq_sum
#print axioms bit_limb_view
#print axioms reconstruction_same
#print axioms amount_checks
#print axioms positive_check
#print axioms initial_checks
#print axioms note_tail_checks
#print axioms pair_checks
#print axioms append_digest_below
#print axioms public_checks
#print axioms note_checks
#print axioms transfer_facts
#print axioms member_transfer_or_copy_collision
end
end AspisV8.SelectedSemanticTransfer
