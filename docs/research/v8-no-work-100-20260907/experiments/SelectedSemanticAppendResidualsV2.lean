import SelectedSemanticOutputTransition

/-!
The literal selected forty append links and the complete 95-position
semantic row oracle supply every field of AppendResiduals on the SAME
table. Public sibling rows are isolated symbolically, including the other
public-digest terms and the dynamic carry term; no summand is deleted.
Zero-weight links supply no unweighted equality. Poseidon round equations,
the direct integer/static afterstate checks, caller/account authority and
actual verifier acceptance remain separate premises/obligations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedSemanticAppendResiduals
open scoped BigOperators
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
open AspisV8.SelectedSemanticOutputTransition
open AspisV8.SelectedNoteRecovery AspisV8.PositivePackBinding
noncomputable section

def appendLink (level : Fin 20) (right : Bool) : Fin 136 :=
  ⟨24 + 2 * level.val + if right then 1 else 0, by cases right <;> simp <;> omega⟩
def targetRow (level : Fin 20) (right : Bool) : Nat :=
  (if right then 544 else 556) + 16 * level.val
def targetStart (right : Bool) : Nat := if right then 8 else 0
def targetOffset (right : Bool) : Nat := if right then 1051521018 else 0

set_option maxRecDepth 1000 in
/-- Forty literal metadata lookups only. Field proofs retain depth200. -/
theorem append_link_shape (level : Fin 20) (right : Bool) :
    selectedKind (appendLink level right) =
      (if right then WeightKind.appendRight level.val else .appendLeft level.val) ∧
    (producer (appendLink level right)).row.val = 539 + 16 * level.val ∧
    (consumer (appendLink level right)).row.val = targetRow level right ∧
    sourcePatterns (producer (appendLink level right)).pattern = ⟨8,0,0⟩ ∧
    sourcePatterns (consumer (appendLink level right)).pattern =
      ⟨8,targetStart right,targetOffset right⟩ := by
  cases right <;> fin_cases level <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Equality is projected only after deriving that this literal public
weight is one. In particular no inactive-link equality is asserted. -/
theorem active_copy_limb (candidate : C1InitialMessages) (index : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer index)
    (level : Fin 20) (right : Bool) (active : index.testBit level.val = right)
    (limb : Fin 8) :
    semanticTable candidate (539 + 16 * level.val) limb.val =
      semanticTable candidate (targetRow level right) (targetStart right + limb.val) +
        if limb.val = 7 then (targetOffset right : F) else 0 := by
  obtain ⟨kind, sourceRow, destinationRow, sourcePattern, destinationPattern⟩ :=
    append_link_shape level right
  have weight : selectedWeight (K := QM31Exact) .transfer index (appendLink level right) = 1 := by
    simp only [selectedWeight, publicWeight, kind]
    cases right <;> simp [weightBit, active]
  let lane : Fin 16 := ⟨limb.val, by omega⟩
  have sourceLive : lane.val < (sourcePatterns (producer (appendLink level right)).pattern).width := by
    rw [sourcePattern]
    exact limb.isLt
  have destinationLive : lane.val < (sourcePatterns (consumer (appendLink level right)).pattern).width := by
    rw [destinationPattern]
    exact limb.isLt
  have equal := aliases (appendLink level right) lane
  rw [weight, one_mul] at equal
  have projected := congrArg (fun value : QM31Exact => value.re.re) (sub_eq_zero.mp equal)
  rw [project_pattern_limb candidate _ lane sourceLive,
    project_pattern_limb candidate _ lane destinationLive, sourcePattern, destinationPattern,
    sourceRow, destinationRow] at projected
  have last : lane.val + 1 = 8 ↔ limb.val = 7 := by dsimp only [lane]; omega
  simpa only [lane, last, Nat.cast_zero, ite_self, add_zero, zero_add] using projected

theorem append_copy_gates (candidate : C1InitialMessages) (index : Nat)
    (aliases : WeightedAliases (memberTable candidate) .transfer index) :
    (∀ (level : Fin 20) (limb : Fin 8),
      (if index.testBit level.val then (0:F) else 1) *
        (SelectedAppendAfterstate.boundary (semanticTable candidate) level.val limb -
          SelectedAppendAfterstate.nodeLeft (semanticTable candidate) level.val limb) = 0) ∧
    (∀ (level : Fin 20) (limb : Fin 8),
      (if index.testBit level.val then (1:F) else 0) *
        (SelectedAppendAfterstate.boundary (semanticTable candidate) level.val limb -
          SelectedAppendAfterstate.literalRight (semanticTable candidate) level.val limb) = 0) := by
  constructor
  · intro level limb
    cases bit : index.testBit level.val with
    | false =>
      simp only [bit, Bool.false_eq_true, if_false, one_mul]
      apply sub_eq_zero.mpr
      simpa [SelectedAppendAfterstate.boundary, SelectedAppendAfterstate.nodeLeft,
        targetRow, targetStart, targetOffset] using
        active_copy_limb candidate index aliases level false bit limb
    | true => simp only [bit, if_true, zero_mul]
  · intro level limb
    cases bit : index.testBit level.val with
    | false => simp only [bit, Bool.false_eq_true, if_false, zero_mul]
    | true =>
      simp only [bit, if_true, one_mul]
      apply sub_eq_zero.mpr
      simpa [SelectedAppendAfterstate.boundary, SelectedAppendAfterstate.literalRight,
        targetRow, targetStart, targetOffset] using
        active_copy_limb candidate index aliases level true bit limb

/-- At an empty-sibling row, the other nineteen sibling terms, every
moved-public term, root and dynamic carry selector are zero. -/
theorem digest_at_empty (pub : Public) (t : BaseTable) (level : Fin 20)
    (empty : pub.appendIndex.testBit level.val = false) (limb : Fin 8) :
    digestResidual pub t (16 * (34 + level.val)) limb =
      t (16 * (34 + level.val)) (8 + limb.val) -
        (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0) := by
  have single : (∑ other : Fin 20,
      if pub.appendIndex.testBit other.val then
        gate (16*(34+level.val) = 16*(34+other.val)+12)
          (t (16*(34+level.val)) limb.val - pub.frontier other limb)
      else gate (16*(34+level.val) = 16*(34+other.val))
        (t (16*(34+level.val)) (8+limb.val) -
          (emptyRoot other limb + if limb.val=7 then NODE_TWEAK else 0))) =
      t (16*(34+level.val)) (8+limb.val) -
        (emptyRoot level limb + if limb.val=7 then NODE_TWEAK else 0) := by
    rw [Finset.sum_eq_single level]
    · simp [empty, gate]
    · intro other _ different
      have distinct : other.val ≠ level.val := fun same => different (Fin.ext same)
      have notLive : 16*(34+level.val) ≠ 16*(34+other.val)+12 := by omega
      have notEmpty : 16*(34+level.val) ≠ 16*(34+other.val) := by omega
      cases bit : pub.appendIndex.testBit other.val <;>
        simp only [bit, Bool.false_eq_true, if_false, if_true, gate,
          if_neg notLive, if_neg notEmpty]
    · simp
  have notAnchor : 16*(34+level.val) ≠ 907 := by omega
  have notNullifier : 16*(34+level.val) ≠ 427 := by omega
  have notOutput0 : 16*(34+level.val) ≠ 475 := by omega
  have notOutput1 : 16*(34+level.val) ≠ 523 := by omega
  have notRoot : 16*(34+level.val) ≠ 859 := by omega
  have notCarry : 16*(34+level.val) ≠
      16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11 := by omega
  unfold digestResidual appendDigestResidual
  rw [single]
  simp [gate, notAnchor, notNullifier, notOutput0, notOutput1, notRoot, notCarry]

theorem digest_at_live (pub : Public) (t : BaseTable) (level : Fin 20)
    (live : pub.appendIndex.testBit level.val = true) (limb : Fin 8) :
    digestResidual pub t (16 * (34 + level.val) + 12) limb =
      t (16 * (34 + level.val) + 12) limb.val - pub.frontier level limb := by
  have single : (∑ other : Fin 20,
      if pub.appendIndex.testBit other.val then
        gate (16*(34+level.val)+12 = 16*(34+other.val)+12)
          (t (16*(34+level.val)+12) limb.val - pub.frontier other limb)
      else gate (16*(34+level.val)+12 = 16*(34+other.val))
        (t (16*(34+level.val)+12) (8+limb.val) -
          (emptyRoot other limb + if limb.val=7 then NODE_TWEAK else 0))) =
      t (16*(34+level.val)+12) limb.val - pub.frontier level limb := by
    rw [Finset.sum_eq_single level]
    · simp [live, gate]
    · intro other _ different
      have distinct : other.val ≠ level.val := fun same => different (Fin.ext same)
      have notLive : 16*(34+level.val)+12 ≠ 16*(34+other.val)+12 := by omega
      have notEmpty : 16*(34+level.val)+12 ≠ 16*(34+other.val) := by omega
      cases bit : pub.appendIndex.testBit other.val <;>
        simp only [bit, Bool.false_eq_true, if_false, if_true, gate,
          if_neg notLive, if_neg notEmpty]
    · simp
  have notAnchor : 16*(34+level.val)+12 ≠ 907 := by omega
  have notNullifier : 16*(34+level.val)+12 ≠ 427 := by omega
  have notOutput0 : 16*(34+level.val)+12 ≠ 475 := by omega
  have notOutput1 : 16*(34+level.val)+12 ≠ 523 := by omega
  have notRoot : 16*(34+level.val)+12 ≠ 859 := by omega
  have notCarry : 16*(34+level.val)+12 ≠
      16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11 := by omega
  unfold digestResidual appendDigestResidual
  rw [single]
  simp [gate, notAnchor, notNullifier, notOutput0, notOutput1, notRoot, notCarry]

theorem append_sibling_checks (pub : Public) (t : BaseTable)
    (vanish : RowsVanish pub t) :
    (∀ level : Fin 20, pub.appendIndex.testBit level.val = false → ∀ limb : Fin 8,
      t (544+16*level.val) (8+limb.val) -
        (extend20 emptyRoot level.val limb + if limb.val=7 then NODE_TWEAK else 0) = 0) ∧
    (∀ level : Fin 20, pub.appendIndex.testBit level.val = true → ∀ limb : Fin 8,
      SelectedAppendAfterstate.nodeLeft t level.val limb -
        extend20 pub.frontier level.val limb = 0) := by
  constructor
  · intro level empty limb
    have zero := zero_at pub t vanish (.digest limb) (16*(34+level.val)) (by omega)
    change digestResidual pub t (16*(34+level.val)) limb = 0 at zero
    rw [digest_at_empty pub t level empty limb] at zero
    have row : 16*(34+level.val) = 544+16*level.val := by omega
    simpa only [row, extend20_at] using zero
  · intro level live limb
    have zero := zero_at pub t vanish (.digest limb) (16*(34+level.val)+12) (by omega)
    change digestResidual pub t (16*(34+level.val)+12) limb = 0 at zero
    rw [digest_at_live pub t level live limb] at zero
    have row : 16*(34+level.val)+12 = 556+16*level.val := by omega
    simpa only [row, SelectedAppendAfterstate.nodeLeft, extend20_at] using zero

theorem append_initial_low (pub : Public) (t : BaseTable)
    (vanish : RowsVanish pub t) (level : Fin 20) (limb : Fin 8) :
    t (16*(34+level.val)) limb.val = 0 := by
  let column : Fin 16 := ⟨limb.val, by omega⟩
  have low : column.val < 8 := limb.isLt
  have modulo : (16*(34+level.val)) % 16 = 0 := by omega
  have quotient : (16*(34+level.val)) / 16 = 34+level.val := by omega
  have notFirst : ¬firstBlock (34+level.val) := by unfold firstBlock; omega
  have node : SelectedSemanticRows.nodeBlock (34+level.val) := by
    unfold SelectedSemanticRows.nodeBlock
    omega
  have notInput : 16*(34+level.val) ≠ 1017 := by omega
  have notOutput : 16*(34+level.val) ≠ 1018 := by omega
  have zero := zero_at pub t vanish (.initial column) (16*(34+level.val)) (by omega)
  simpa [SelectedSemanticRows.residual, SelectedSemanticRows.initialResidual,
    modulo, quotient, notFirst, node, low, occupancyResidual, gate,
    notInput, notOutput, column] using zero

/-- All six original append-local prerequisites, with the literal selected
empty roots and same early table. No append success is assumed. -/
theorem append_residuals (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex) :
    SelectedAppendAfterstate.AppendResiduals rc (semanticTable candidate)
      pub.appendIndex (extend20 emptyRoot) (extend20 pub.frontier) := by
  have copies := append_copy_gates candidate pub.appendIndex aliases
  have siblings := append_sibling_checks pub (semanticTable candidate) vanish
  exact ⟨copies.1, copies.2, siblings.1, siblings.2,
    append_initial_low pub (semanticTable candidate) vanish,
    fun level => poseidon ⟨34+level.val, by omega⟩⟩

/-- The previous transition endpoint no longer needs caller-supplied
AppendResiduals. Integer/static/dynamic AfterstateChecks remain explicit. -/
theorem semantic_transfer_transition (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (sequence nextIndex : Nat)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex)
    (direct : SelectedAppendAfterstate.AfterstateChecks (semanticTable candidate)
      sequence pub.appendIndex nextIndex (extend20 emptyRoot) (extend20 pub.frontier)
      (extend20 pub.nextFrontier) pub.nextRoot) :
    TransferTransitionFacts rc pub candidate sequence nextIndex :=
  SelectedSemanticOutputTransition.semantic_transfer_transition rc pub candidate sequence nextIndex
    vanish poseidon aliases (append_residuals rc pub candidate vanish poseidon aliases) direct

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
      ((packedRows_zero_iff pub _).mp packedZero) poseidon aliases direct)
  · exact Or.inr collision

#print axioms append_link_shape
#print axioms active_copy_limb
#print axioms append_copy_gates
#print axioms digest_at_empty
#print axioms digest_at_live
#print axioms append_sibling_checks
#print axioms append_initial_low
#print axioms append_residuals
#print axioms semantic_transfer_transition
#print axioms member_transition_or_copy_collision
end
end AspisV8.SelectedSemanticAppendResiduals
