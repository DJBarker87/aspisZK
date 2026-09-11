import SelectedSemanticTransferV2

/-!
The same selected positive-transfer table now supplies the actual output-pair
constructor and its append leaf. Literal links20/21/23, output occupancy,
node initial zeros and the existing two-round gates derive the missing
OutputPairResiduals; neither validator success nor a nonzero sentinel is a
premise. Explicit append-local and direct integer/frontier checks then feed
the existing selected afterstate theorem. Authentication, historical input
membership, deployed Poseidon faithfulness and actual acceptance remain open.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedSemanticOutputTransition
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7ExtractedLaneWords AspisPool.V7FixedWidth29TupleList
open AspisPool.V7C1SubfieldRecovery
open AspisV8.SelectedWeightedCopyCore AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedCopyAliases AspisV8.SelectedCopyAliasQM31
open AspisV8.EarlyC1CopyCollision AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedEarlyC1InputPair AspisV8.SelectedEarlyC1PaymentFacts
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedNoteRecovery AspisV8.SelectedOutputNotes
open AspisV8.SelectedOutputPair AspisV8.PositivePackBinding
noncomputable section

def outputLink : Fin 3 → Fin 136 := ![20,21,23]
def outputSourceRow : Fin 3 → Nat := ![523,475,1018]
def outputTargetRow : Fin 3 → Nat := ![1018,540,528]
def outputSourceStart : Fin 3 → Nat := ![0,0,2]
def outputTargetStart : Fin 3 → Nat := ![2,0,8]
def outputTargetOffset : Fin 3 → Nat := ![0,0,1051521018]

set_option maxRecDepth 1000 in
/-- Three literal metadata entries only, as in the already-green input-pair
certificate. All field/table proofs retain depth200. The withdrawal-only
link22 is not substituted for the active transfer link21. -/
theorem output_link_shape (edge : Fin 3) :
    transferKind (selectedKind (outputLink edge)) = true ∧
    (producer (outputLink edge)).row.val = outputSourceRow edge ∧
    (consumer (outputLink edge)).row.val = outputTargetRow edge ∧
    sourcePatterns (producer (outputLink edge)).pattern =
      ⟨8, outputSourceStart edge, 0⟩ ∧
    sourcePatterns (consumer (outputLink edge)).pattern =
      ⟨8, outputTargetStart edge, outputTargetOffset edge⟩ := by
  fin_cases edge <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Public weight one is derived at the three selected transfer entries.
Projection is applied to an equality, not to arbitrary QM31 products. -/
theorem output_copy_limb (candidate : C1InitialMessages) (appendIndex : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer appendIndex)
    (edge : Fin 3) (limb : Fin 8) :
    semanticTable candidate (outputSourceRow edge) (outputSourceStart edge + limb.val) =
      semanticTable candidate (outputTargetRow edge) (outputTargetStart edge + limb.val) +
        if limb.val = 7 then (outputTargetOffset edge : F) else 0 := by
  obtain ⟨kind, sourceRow, targetRow, sourcePattern, targetPattern⟩ := output_link_shape edge
  have weight : selectedWeight (K := QM31Exact) .transfer appendIndex (outputLink edge) = 1 :=
    transfer_kind_weight _ appendIndex kind
  let lane : Fin 16 := ⟨limb.val, by omega⟩
  have sourceLive : lane.val < (sourcePatterns (producer (outputLink edge)).pattern).width := by
    rw [sourcePattern]
    exact limb.isLt
  have targetLive : lane.val < (sourcePatterns (consumer (outputLink edge)).pattern).width := by
    rw [targetPattern]
    exact limb.isLt
  have equal := aliases (outputLink edge) lane
  rw [weight, one_mul] at equal
  have projected := congrArg (fun value : QM31Exact => value.re.re) (sub_eq_zero.mp equal)
  rw [project_pattern_limb candidate _ lane sourceLive,
    project_pattern_limb candidate _ lane targetLive, sourcePattern, targetPattern,
    sourceRow, targetRow] at projected
  have last : lane.val + 1 = 8 ↔ limb.val = 7 := by dsimp only [lane]; omega
  simpa only [lane, last, Nat.cast_zero, ite_self, add_zero] using projected

theorem output_pair_copies (candidate : C1InitialMessages) (appendIndex : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer appendIndex) :
    (∀ i : Fin 8, semanticTable candidate 523 i.val -
      semanticTable candidate 1018 (2+i.val) = 0) ∧
    (∀ i : Fin 8, semanticTable candidate 475 i.val -
      semanticTable candidate 540 i.val = 0) ∧
    (∀ i : Fin 8, semanticTable candidate 1018 (2+i.val) -
      rightInput (semanticTable candidate) i = 0) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    apply sub_eq_zero.mpr
    simpa [outputSourceRow, outputTargetRow, outputSourceStart,
      outputTargetStart, outputTargetOffset] using output_copy_limb candidate appendIndex aliases 0 i
  · intro i
    apply sub_eq_zero.mpr
    simpa [outputSourceRow, outputTargetRow, outputSourceStart,
      outputTargetStart, outputTargetOffset] using output_copy_limb candidate appendIndex aliases 1 i
  · intro i
    apply sub_eq_zero.mpr
    simpa [outputSourceRow, outputTargetRow, outputSourceStart,
      outputTargetStart, outputTargetOffset, rightInput] using
      output_copy_limb candidate appendIndex aliases 2 i

/-- Output occupancy is derived from positions11 and1 at row1018; the
entire 95-position oracle remains a premise, not a weakened acceptance test. -/
theorem output_pair_semantic (pub : Public) (t : BaseTable)
    (vanish : RowsVanish pub t) :
    t 1018 0 - 1 = 0 ∧ t 1018 9 * t 1018 1 - t 1018 0 = 0 ∧
    (∀ i : Fin 8, t 528 i.val = 0) := by
  refine ⟨?_,?_,?_⟩
  · simpa [SelectedSemanticRows.residual, SelectedSemanticRows.initialResidual,
      gate, occupancyResidual] using
      zero_at pub t vanish (.initial ⟨11, by decide⟩) 1018 (by decide)
  · simpa [SelectedSemanticRows.residual, SelectedSemanticRows.initialResidual,
      gate, occupancyResidual] using
      zero_at pub t vanish (.initial ⟨1, by decide⟩) 1018 (by decide)
  · intro i
    let column : Fin 16 := ⟨i.val, by omega⟩
    have low : column.val < 8 := i.isLt
    simpa [SelectedSemanticRows.residual, SelectedSemanticRows.initialResidual,
      gate, occupancyResidual, firstBlock, SelectedSemanticRows.nodeBlock, low, column] using
      zero_at pub t vanish (.initial column) 528 (by decide)

theorem output_pair_residuals (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    OutputPairResiduals rc (semanticTable candidate) := by
  have copies := output_pair_copies candidate pub.appendIndex aliases
  have semantic := output_pair_semantic pub (semanticTable candidate) vanish
  exact ⟨semantic.1, semantic.2.1, copies.1, copies.2.1, copies.2.2,
    semantic.2.2, poseidon ⟨33, by decide⟩⟩

/-- A genuinely checked field-stage constructor and its actual hash input.
The change sentinel is not assumed nonzero and the inverse is not supplied. -/
theorem checked_public_output_pair (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    pub.commitments 1 7 ≠ 0 ∧
    twoOutputsFields (pub.commitments 0) (pub.commitments 1) =
      some (computedPair (pub.commitments 0) (pub.commitments 1)) ∧
    pairDigest (semanticTable candidate) = nodeHash rc (pub.commitments 0) (pub.commitments 1) := by
  have bindings := (public_checks pub (semanticTable candidate) vanish).2.2.2
  apply public_output_pair_endpoint rc (semanticTable candidate)
    (output_pair_residuals rc pub candidate vanish poseidon aliases)
  · simpa [outputBlock] using bindings 0
  · simpa [outputBlock] using bindings 1

/-- Total view used only to call the already-green Nat-indexed append API.
The real twenty entries are unchanged; no arbitrary empty-root array is used. -/
def extend20 (values : Fin 20 → Digest) (level : Nat) : Digest :=
  if bounded : level < 20 then values ⟨level,bounded⟩ else fun _ => 0

theorem extend20_at (values : Fin 20 → Digest) (level : Fin 20) :
    extend20 values level.val = values level := by
  simp only [extend20, dif_pos level.isLt]

/-- This slice combines actual payment facts, checked output-pair construction,
and the exact selected append afterstate. It is not full historical input
membership, authenticated caller authority, or a verifier acceptance record. -/
def TransferTransitionFacts (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (sequence nextIndex : Nat) : Prop :=
  TransferFacts rc candidate pub.asset pub.nullifier pub.commitments ∧
  pub.commitments 1 7 ≠ 0 ∧
  twoOutputsFields (pub.commitments 0) (pub.commitments 1) =
    some (computedPair (pub.commitments 0) (pub.commitments 1)) ∧
  nextIndex = sequence+1 ∧ nextIndex ≤ 2^20 ∧
  pub.nextRoot = SelectedAppendAfterstate.computedAt rc pub.appendIndex
    (extend20 emptyRoot) (extend20 pub.frontier)
    (nodeHash rc (pub.commitments 0) (pub.commitments 1)) 20 ∧
  ∀ level : Fin 20, pub.nextFrontier level =
    SelectedAppendAfterstate.computedFrontier rc pub.appendIndex
      (extend20 emptyRoot) (extend20 pub.frontier)
      (nodeHash rc (pub.commitments 0) (pub.commitments 1)) level.val

theorem transfer_and_afterstate (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (sequence nextIndex : Nat)
    (facts : TransferFacts rc candidate pub.asset pub.nullifier pub.commitments)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex)
    (append : SelectedAppendAfterstate.AppendResiduals rc (semanticTable candidate)
      pub.appendIndex (extend20 emptyRoot) (extend20 pub.frontier))
    (direct : SelectedAppendAfterstate.AfterstateChecks (semanticTable candidate)
      sequence pub.appendIndex nextIndex (extend20 emptyRoot) (extend20 pub.frontier)
      (extend20 pub.nextFrontier) pub.nextRoot) :
    TransferTransitionFacts rc pub candidate sequence nextIndex := by
  have bindings := (public_checks pub (semanticTable candidate) vanish).2.2.2
  have transition := SelectedAppendAfterstate.public_output_pair_afterstate rc
    (semanticTable candidate) sequence pub.appendIndex nextIndex
    (extend20 emptyRoot) (extend20 pub.frontier) (extend20 pub.nextFrontier)
    pub.nextRoot (pub.commitments 0) (pub.commitments 1)
    (output_pair_residuals rc pub candidate vanish poseidon aliases) append direct
    (by simpa [outputBlock] using bindings 0) (by simpa [outputBlock] using bindings 1)
  exact ⟨facts, transition.1, transition.2.1, transition.2.2.1,
    transition.2.2.2.1, transition.2.2.2.2.1,
    fun level => (extend20_at pub.nextFrontier level).symm.trans (transition.2.2.2.2.2 level)⟩

/-- All same-table payment facts are obtained from the residual oracle,
not supplied as a valid witness or successful decoder assumption. -/
theorem semantic_transfer_transition (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (sequence nextIndex : Nat)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex)
    (append : SelectedAppendAfterstate.AppendResiduals rc (semanticTable candidate)
      pub.appendIndex (extend20 emptyRoot) (extend20 pub.frontier))
    (direct : SelectedAppendAfterstate.AfterstateChecks (semanticTable candidate)
      sequence pub.appendIndex nextIndex (extend20 emptyRoot) (extend20 pub.frontier)
      (extend20 pub.nextFrontier) pub.nextRoot) :
    TransferTransitionFacts rc pub candidate sequence nextIndex :=
  transfer_and_afterstate rc pub candidate sequence nextIndex
    (transfer_facts rc pub candidate vanish poseidon aliases) vanish poseidon aliases append direct

/-- One pre-lambda early-C1 family member and one sequential copy-collision
alternative, with every pole and helper boundary retained in CopyConditions.
The recovered tuple's membership/authentication is not inferred here. -/
theorem member_transition_or_copy_collision (rc : RoundConstants) (pub : Public)
    (c1 : C1InitialWords) (candidate : C1InitialMessages) (sequence nextIndex : Nat)
    (member : candidate ∈ EarlyC1Family.family c1)
    (baseWord : ∀ column index, projectBase (c1 column index) = c1 column index)
    (lambdas chis : Finset QM31Exact) (lambda chi : QM31Exact)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → QM31Exact)
    (copy : CopyConditions candidate .transfer pub.appendIndex lambda chi helper)
    (packedZero : ∀ row group, packedRows pub (semanticTable candidate) row group = 0)
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (append : SelectedAppendAfterstate.AppendResiduals rc (semanticTable candidate)
      pub.appendIndex (extend20 emptyRoot) (extend20 pub.frontier))
    (direct : SelectedAppendAfterstate.AfterstateChecks (semanticTable candidate)
      sequence pub.appendIndex nextIndex (extend20 emptyRoot) (extend20 pub.frontier)
      (extend20 pub.nextFrontier) pub.nextRoot) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable candidate row.val column.val) = memberTable candidate row column.val) ∧
    (TransferTransitionFacts rc pub candidate sequence nextIndex ∨
      (lambda,chi) ∈ collisionPairs c1 .transfer pub.appendIndex lambdas chis) := by
  refine ⟨semanticTable_embeds c1 candidate member baseWord, ?_⟩
  rcases source_member_covered c1 .transfer pub.appendIndex lambdas chis lambda chi
      lambdaMember chiMember candidate member helper copy with aliases | collision
  · exact Or.inl (semantic_transfer_transition rc pub candidate sequence nextIndex
      ((packedRows_zero_iff pub _).mp packedZero) poseidon aliases append direct)
  · exact Or.inr collision

#print axioms output_link_shape
#print axioms output_copy_limb
#print axioms output_pair_copies
#print axioms output_pair_semantic
#print axioms output_pair_residuals
#print axioms checked_public_output_pair
#print axioms extend20_at
#print axioms transfer_and_afterstate
#print axioms semantic_transfer_transition
#print axioms member_transition_or_copy_collision
end
end AspisV8.SelectedSemanticOutputTransition
