import SelectedCopyLayout

/-! Selected generated endpoints/patterns to Boolean row values/weights.
The source's additive endpoint accumulation is modeled as a finite sum;
zero public weight does not remove that endpoint's compressed value.
The literal layout certificate discharges the previously explicit
inactiveWeights prerequisite of SelectedWeightedCopyRows.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.SelectedCopyLayoutRows
open scoped BigOperators
open AspisV8.SelectedWeightedCopyCore
open AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout

variable {K : Type*} [Field K]

/-- A total table read interface. The bound below proves that every live
pattern read lies in columns0..15; rows are already Fin1024. -/
abbrev Table (K : Type*) := Fin 1024 → Nat → K

def patternLimb (table : Table K) (endpoint : Endpoint) (limb : Fin 16) : K :=
  let pattern := sourcePatterns endpoint.pattern
  if limb.val < pattern.width then
    table endpoint.row (pattern.start + limb.val) +
      if limb.val + 1 = pattern.width then (pattern.lastOffset : K) else 0
  else 0

theorem pattern_read_in_range (pattern : Fin 14) (limb : Fin 16)
    (live : limb.val < (sourcePatterns pattern).width) :
    (sourcePatterns pattern).start + limb.val < 16 :=
  (Nat.add_lt_add_left live _).trans_le (source_pattern_ranges pattern)

/-- Literal tag + lambda*limb0 + ... + lambda^16*limb15.
The public offset is retained in pattern10's last active limb. -/
def compressed (table : Table K) (lambda : K)
    (index : Fin 136) (endpoint : Endpoint) : K :=
  (selectedTag index : K) +
    ∑ limb : Fin 16, lambda ^ (limb.val + 1) * patternLimb table endpoint limb

def slotContribution (endpoint : Endpoint) (row : Fin 1024) (slot : Fin 2)
    (value : K) : K :=
  if endpoint.row = row ∧ endpoint.slot = slot then value else 0

def gather (endpoint : Fin 136 → Endpoint) (value : Fin 136 → K)
    (row : Fin 1024) (slot : Fin 2) : K :=
  ∑ index : Fin 136, slotContribution (endpoint index) row slot (value index)

/-- This models the fixed compiled-slot path. It is not the independent
host constructor which searches for a slot by zero public weight. -/
def sourceRows (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (row : Fin 1024) : Row K where
  producerValue := gather (fun index => (sourceLinks index).producer)
    (fun index => compressed table lambda index (sourceLinks index).producer) row
  producerWeight := gather (fun index => (sourceLinks index).producer)
    (selectedWeight variant appendIndex) row
  consumerValue := gather (fun index => (sourceLinks index).consumer)
    (fun index => compressed table lambda index (sourceLinks index).consumer) row
  consumerWeight := gather (fun index => (sourceLinks index).consumer)
    (selectedWeight variant appendIndex) row

theorem slotContribution_outside (endpoint : Endpoint)
    (inside : rowActive endpoint.row) (row : Fin 1024)
    (outside : ¬rowActive row) (slot : Fin 2) (value : K) :
    slotContribution endpoint row slot value = 0 := by
  apply if_neg
  intro hit
  exact outside (hit.1 ▸ inside)

theorem gather_outside (endpoint : Fin 136 → Endpoint)
    (inside : ∀ index, rowActive (endpoint index).row)
    (value : Fin 136 → K) (row : Fin 1024)
    (outside : ¬rowActive row) (slot : Fin 2) :
    gather endpoint value row slot = 0 := by
  apply Finset.sum_eq_zero
  intro index _
  exact slotContribution_outside (endpoint index) (inside index)
    row outside slot (value index)

/-- No caller-supplied inactive-weight condition: every occurrence is
checked in source_endpoints_active, including public zero-weight links. -/
theorem sourceRows_inactive_weights (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (row : Fin 1024)
    (outside : ¬rowActive row) :
    (∀ slot, (sourceRows table lambda variant appendIndex row).producerWeight slot = 0) ∧
      ∀ slot, (sourceRows table lambda variant appendIndex row).consumerWeight slot = 0 := by
  constructor
  · intro slot
    exact gather_outside (fun index => (sourceLinks index).producer)
      (fun index => (source_endpoints_active index).1)
      (selectedWeight variant appendIndex) row outside slot
  · intro slot
    exact gather_outside (fun index => (sourceLinks index).consumer)
      (fun index => (source_endpoints_active index).2)
      (selectedWeight variant appendIndex) row outside slot

/-- The source value sums also vanish outside the fixed mask, without
making the incorrect claim that a zero-weight active slot has zero value. -/
theorem sourceRows_inactive_values (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (row : Fin 1024)
    (outside : ¬rowActive row) :
    (∀ slot, (sourceRows table lambda variant appendIndex row).producerValue slot = 0) ∧
      ∀ slot, (sourceRows table lambda variant appendIndex row).consumerValue slot = 0 := by
  constructor
  · intro slot
    exact gather_outside (fun index => (sourceLinks index).producer)
      (fun index => (source_endpoints_active index).1)
      (fun index => compressed table lambda index (sourceLinks index).producer)
      row outside slot
  · intro slot
    exact gather_outside (fun index => (sourceLinks index).consumer)
      (fun index => (source_endpoints_active index).2)
      (fun index => compressed table lambda index (sourceLinks index).consumer)
      row outside slot

/-- The new layout theorem discharges exactly the old static prerequisite.
Local row correctness, both helper sums and ALL active-row slot poles remain
explicit; acceptance, decoder success and payment validity are not assumed. -/
theorem source_layout_balance_zero (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (helper : Fin 1024 → K) (chi : K)
    (localZero : ∀ row,
      selectedBooleanResidual (sourceRows table lambda variant appendIndex)
        helper chi row = 0)
    (totalZero : (∑ row, helper row) = 0)
    (inactiveZero : (∑ row, inactiveHelper rowActive helper row) = 0)
    (noPole : ∀ row, rowActive row →
      NoSlotPole (sourceRows table lambda variant appendIndex row) chi) :
    (∑ row, rationalContribution (sourceRows table lambda variant appendIndex row) chi) = 0 := by
  apply selected_whole_balance_zero
    (sourceRows table lambda variant appendIndex) helper chi
    localZero totalZero inactiveZero noPole
  intro row outside
  exact sourceRows_inactive_weights table lambda variant appendIndex row outside

#print axioms pattern_read_in_range
#print axioms slotContribution_outside
#print axioms gather_outside
#print axioms sourceRows_inactive_weights
#print axioms sourceRows_inactive_values
#print axioms source_layout_balance_zero
end AspisV8.SelectedCopyLayoutRows
