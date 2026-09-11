import SelectedSemanticAppendResidualsV2

/-!
The two remaining table-dependent AfterstateChecks are actual digest-row
projections. Literal public comparisons from validate_transition then
construct the whole record, retaining their external source justification
and the u64 trailing_ones-to-carryScan correspondence explicitly.

Neither public comparisons nor account authentication alone can provide
the table equations: the index-zero/zero-table counterexample below keeps
this boundary visible. No Rust/PDA/CPI execution refinement is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedSemanticAfterstateChecks
open scoped BigOperators
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisPool.V7FixedWidth29TupleList
open AspisV8.SelectedNoteRecovery AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedCopyAliases AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedSemanticOutputTransition
noncomputable section

/-- Unlike the sibling rows, root and carry rows are 11 modulo16.
All twenty sibling summands vanish individually at such a row. -/
theorem sibling_sum_at_eleven (pub : Public) (t : BaseTable) (row : Nat)
    (localRow : row % 16 = 11) (limb : Fin 8) :
    (∑ level : Fin 20,
      if pub.appendIndex.testBit level.val then
        gate (row = 16*(34+level.val)+12) (t row limb.val-pub.frontier level limb)
      else gate (row = 16*(34+level.val))
        (t row (8+limb.val) -
          (emptyRoot level limb + if limb.val=7 then NODE_TWEAK else 0))) = 0 := by
  apply Finset.sum_eq_zero
  intro level _
  have notLive : row ≠ 16*(34+level.val)+12 := by omega
  have notEmpty : row ≠ 16*(34+level.val) := by omega
  cases bit : pub.appendIndex.testBit level.val <;>
    simp only [bit, Bool.false_eq_true, if_false, if_true, gate,
      if_neg notLive, if_neg notEmpty]

theorem digest_at_root (pub : Public) (t : BaseTable) (limb : Fin 8) :
    digestResidual pub t 859 limb = t 859 limb.val-pub.nextRoot limb := by
  have others : (859:Nat) ≠ 907 ∧ 859 ≠ 427 ∧ 859 ≠ 475 ∧ 859 ≠ 523 := by decide
  have notCarry (within : SelectedAppendAfterstate.carryIndex pub.appendIndex < 20) :
      859 ≠ 16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11 := by omega
  unfold digestResidual appendDigestResidual
  rw [sibling_sum_at_eleven pub t 859 (by decide) limb]
  by_cases within : SelectedAppendAfterstate.carryIndex pub.appendIndex < 20
  · simp only [gate, if_neg others.1, if_neg others.2.1,
      if_neg others.2.2.1, if_neg others.2.2.2, if_true,
      dif_pos within, if_neg (notCarry within), zero_add, add_zero]
  · simp only [gate, if_neg others.1, if_neg others.2.1,
      if_neg others.2.2.1, if_neg others.2.2.2, if_true,
      dif_neg within, zero_add, add_zero]

theorem digest_at_carry (pub : Public) (t : BaseTable)
    (within : SelectedAppendAfterstate.carryIndex pub.appendIndex < 20) (limb : Fin 8) :
    digestResidual pub t (16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11) limb =
      t (16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11) limb.val -
        pub.nextFrontier ⟨SelectedAppendAfterstate.carryIndex pub.appendIndex,within⟩ limb := by
  let row := 16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11
  have localRow : row % 16 = 11 := by dsimp only [row]; omega
  have notAnchor : row ≠ 907 := by dsimp only [row]; omega
  have notNullifier : row ≠ 427 := by dsimp only [row]; omega
  have notOutput0 : row ≠ 475 := by dsimp only [row]; omega
  have notOutput1 : row ≠ 523 := by dsimp only [row]; omega
  have notRoot : row ≠ 859 := by dsimp only [row]; omega
  change digestResidual pub t row limb = t row limb.val -
    pub.nextFrontier ⟨SelectedAppendAfterstate.carryIndex pub.appendIndex,within⟩ limb
  unfold digestResidual appendDigestResidual
  rw [sibling_sum_at_eleven pub t row localRow limb]
  simp only [gate, if_neg notAnchor, if_neg notNullifier, if_neg notOutput0,
    if_neg notOutput1, if_neg notRoot, dif_pos within, if_true, zero_add]

/-- These two facts require the SAME table's actual rows, not merely an
authenticated source cursor or canonical proposed afterstate bytes. -/
theorem dynamic_bindings (pub : Public) (t : BaseTable) (vanish : RowsVanish pub t) :
    (SelectedAppendAfterstate.carryIndex pub.appendIndex < 20 → ∀ limb : Fin 8,
      SelectedAppendAfterstate.boundary t (SelectedAppendAfterstate.carryIndex pub.appendIndex) limb -
        extend20 pub.nextFrontier (SelectedAppendAfterstate.carryIndex pub.appendIndex) limb = 0) ∧
    (∀ limb : Fin 8, t 859 limb.val-pub.nextRoot limb=0) := by
  constructor
  · intro within limb
    have zero := zero_at pub t vanish (.digest limb)
      (16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11) (by omega)
    change digestResidual pub t
      (16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11) limb = 0 at zero
    rw [digest_at_carry pub t within limb] at zero
    have row : 16*(33+SelectedAppendAfterstate.carryIndex pub.appendIndex)+11 =
      539+16*SelectedAppendAfterstate.carryIndex pub.appendIndex := by omega
    simpa only [SelectedAppendAfterstate.boundary, extend20, dif_pos within, row] using zero
  · intro limb
    have zero := zero_at pub t vanish (.digest limb) 859 (by decide)
    change digestResidual pub t 859 limb = 0 at zero
    rwa [digest_at_root pub t limb] at zero

/-- The literal successful validate_transition comparisons, restricted to
the fields used by AfterstateChecks. Pool/deployment equality, canonical
word parsing and independent account authority are not encoded here.
The Rust-computed carry is an external parameter, never identified with
the modeled scan by definition. The source's exact skip condition is kept. -/
def SourceComparisons (pub : Public) (sequence nextIndex rustCarry : Nat) : Prop :=
  sequence = pub.appendIndex ∧ pub.appendIndex < 2^20 ∧
  nextIndex = pub.appendIndex+1 ∧
  ∀ level : Fin 20, ¬(level.val=rustCarry ∧ rustCarry<20) →
    pub.nextFrontier level =
      if level.val<rustCarry ∨ pub.appendIndex.testBit level.val=false
      then emptyRoot level else pub.frontier level

/-- The only new assembly is the two derived table bindings. Caller-side
comparisons and the native carry correspondence are explicit prerequisites. -/
theorem afterstate_checks (pub : Public) (t : BaseTable) (sequence nextIndex rustCarry : Nat)
    (vanish : RowsVanish pub t)
    (comparisons : SourceComparisons pub sequence nextIndex rustCarry)
    (carryExact : rustCarry = SelectedAppendAfterstate.carryIndex pub.appendIndex) :
    SelectedAppendAfterstate.AfterstateChecks t sequence pub.appendIndex nextIndex
      (extend20 emptyRoot) (extend20 pub.frontier) (extend20 pub.nextFrontier) pub.nextRoot := by
  have dynamic := dynamic_bindings pub t vanish
  refine ⟨comparisons.1, comparisons.2.1, comparisons.2.2.1, ?_, dynamic.1, dynamic.2⟩
  intro level notCarry
  have source := comparisons.2.2.2 level (by
    intro skipped
    exact notCarry (skipped.1.trans carryExact))
  simpa only [extend20_at, carryExact] using source

theorem semantic_transfer_transition (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (sequence nextIndex rustCarry : Nat)
    (vanish : RowsVanish pub (semanticTable candidate))
    (poseidon : PoseidonChecks rc (semanticTable candidate))
    (aliases : WeightedAliases (memberTable candidate) .transfer pub.appendIndex)
    (comparisons : SourceComparisons pub sequence nextIndex rustCarry)
    (carryExact : rustCarry = SelectedAppendAfterstate.carryIndex pub.appendIndex) :
    TransferTransitionFacts rc pub candidate sequence nextIndex :=
  SelectedSemanticAppendResiduals.semantic_transfer_transition rc pub candidate sequence nextIndex
    vanish poseidon aliases (afterstate_checks pub (semanticTable candidate) sequence nextIndex
      rustCarry vanish comparisons carryExact)

/-- Canonical source-shaped index-zero public proposal. Only the candidate
root's first base limb is one; no proof or RowsVanish is postulated. -/
def indexZeroProposal : Public where
  asset := 0
  anchor := fun _ => 0
  nullifier := fun _ => 0
  commitments := fun _ _ => 0
  appendIndex := 0
  frontier := emptyRoot
  nextRoot := fun limb => if limb.val=0 then 1 else 0
  nextFrontier := emptyRoot

theorem zero_index_carry : SelectedAppendAfterstate.carryIndex 0 = 0 := by
  have spec := SelectedAppendAfterstate.carry_scan_spec (Nat.testBit 0) 20
  by_contra nonzero
  have positive : 0 < SelectedAppendAfterstate.carryScan (Nat.testBit 0) 20 := by
    change SelectedAppendAfterstate.carryScan (Nat.testBit 0) 20 ≠ 0 at nonzero
    omega
  have impossible := spec.1 0 positive
  change false = true at impossible
  exact Bool.false_ne_true impossible

/-- Regression against auth+static => table equations. The literal public
comparisons and exact carry hold, yet the zero table cannot have the proposed
root e0. This is NOT a counterexample to accepted verification. -/
theorem source_comparisons_do_not_force_table_binding :
    SourceComparisons indexZeroProposal 0 1 0 ∧
    0 = SelectedAppendAfterstate.carryIndex indexZeroProposal.appendIndex ∧
    ¬SelectedAppendAfterstate.AfterstateChecks (fun _ _ => 0) 0 0 1
      (extend20 emptyRoot) (extend20 emptyRoot) (extend20 emptyRoot) indexZeroProposal.nextRoot := by
  refine ⟨?_, zero_index_carry.symm, ?_⟩
  · refine ⟨rfl, by decide, rfl, ?_⟩
    intro level _
    change emptyRoot level = if level.val<0 ∨ (0:Nat).testBit level.val=false
      then emptyRoot level else emptyRoot level
    split <;> rfl
  · intro checked
    have impossible := checked.rootBinding ⟨0, by decide⟩
    change (0:F)-(1:F)=0 at impossible
    exact zero_ne_one (sub_eq_zero.mp impossible)

#print axioms sibling_sum_at_eleven
#print axioms digest_at_root
#print axioms digest_at_carry
#print axioms dynamic_bindings
#print axioms afterstate_checks
#print axioms semantic_transfer_transition
#print axioms zero_index_carry
#print axioms source_comparisons_do_not_force_table_binding
end
end AspisV8.SelectedSemanticAfterstateChecks
