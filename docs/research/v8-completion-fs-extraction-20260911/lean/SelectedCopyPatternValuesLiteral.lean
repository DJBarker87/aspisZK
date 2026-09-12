import SelectedCopyDescriptorAggregation

/-! Literal fourteen-pattern Copy compressor.

This is the smallest source-shaped model of `pattern_values_literal` in
`pair_forest_copy_terminal.rs`.  It records the fourteen outputs in their
Rust order, the repeated-multiplication power schedule beginning at `lambda`,
the live prefix of each pattern, its source-column start, and the sole public
offset.  The theorem identifies every output with the compact
`sourcePatterns` expression consumed by `compressed`.

This file intentionally does not identify Rust `COPY_LINKS` with Lean
`sourceLinks`, nor Rust tag/weight-kind fields with `selectedTag` and
`selectedKind`; that finite constant-table refinement remains separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedCopyPatternValuesLiteral
open scoped BigOperators
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedWeightedCopyRows

variable {K : Type*} [Field K]

/-- Independent compact transcription of the live portions of the literal
Rust `COPY_PATTERNS` array, in exact output order.  Inactive Rust cells do not
enter `pattern_values_literal` because their `kind` is zero. -/
def rustPatterns : Fin 14 → Pattern := ![
  ⟨16,0,0⟩, ⟨8,0,0⟩, ⟨6,2,0⟩, ⟨6,0,0⟩,
  ⟨2,0,0⟩, ⟨2,6,0⟩, ⟨1,0,0⟩, ⟨1,10,0⟩,
  ⟨1,1,0⟩, ⟨1,2,0⟩, ⟨8,8,1051521018⟩,
  ⟨8,2,0⟩, ⟨8,1,0⟩, ⟨8,8,0⟩]

/-- Static order/range/offset correspondence.  This is independent of field
values and challenges. -/
theorem rustPatterns_eq_sourcePatterns : rustPatterns = sourcePatterns := by
  funext pattern
  fin_cases pattern <;> decide

/-- Value in the Rust `powers[limb]` cell after starting with `power=lambda`
and multiplying once at the end of every preceding loop iteration. -/
def rustPowerAt (lambda : K) : Nat → K
  | 0 => lambda
  | limb + 1 => rustPowerAt lambda limb * lambda

theorem rustPowerAt_eq_pow (lambda : K) (limb : Nat) :
    rustPowerAt lambda limb = lambda ^ (limb + 1) := by
  induction limb with
  | zero => simp [rustPowerAt]
  | succ limb ih =>
      rw [rustPowerAt, ih]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (pow_succ lambda (limb + 1)).symm

/-- One output of the literal nested loop.  `openings` is total only to avoid
mixing an array-bounds refinement into this field identity; the static range
theorem below proves every live column is below sixteen. -/
def rustPatternValueLiteral (openings : Nat → K) (lambda : K)
    (pattern : Fin 14) : K :=
  ∑ limb : Fin 16,
    let descriptor := rustPatterns pattern
    if limb.val < descriptor.width then
      rustPowerAt lambda limb.val *
        (openings (descriptor.start + limb.val) +
          if limb.val + 1 = descriptor.width then
            (descriptor.lastOffset : K)
          else 0)
    else 0

/-- Compact field specification used by `SelectedCopyLayoutRows`. -/
def sourcePatternValue (openings : Nat → K) (lambda : K)
    (pattern : Fin 14) : K :=
  ∑ limb : Fin 16,
    let descriptor := sourcePatterns pattern
    lambda ^ (limb.val + 1) *
      if limb.val < descriptor.width then
        openings (descriptor.start + limb.val) +
          if limb.val + 1 = descriptor.width then
            (descriptor.lastOffset : K)
          else 0
      else 0

/-- Exact field-level output identity for every one of the fourteen Rust
result slots.  It fixes the first power at `lambda` (not one), all additions,
column starts, prefix widths, and pattern10's last-limb offset. -/
theorem rustPatternValueLiteral_eq_sourcePatternValue
    (openings : Nat → K) (lambda : K) (pattern : Fin 14) :
    rustPatternValueLiteral openings lambda pattern =
      sourcePatternValue openings lambda pattern := by
  classical
  unfold rustPatternValueLiteral sourcePatternValue
  rw [rustPatterns_eq_sourcePatterns]
  apply Finset.sum_congr rfl
  intro limb _
  rw [rustPowerAt_eq_pow]
  by_cases live : limb.val < (sourcePatterns pattern).width
  · simp [live]
  · simp [live]

theorem rust_live_column_in_range (pattern : Fin 14) (limb : Fin 16)
    (live : limb.val < (rustPatterns pattern).width) :
    (rustPatterns pattern).start + limb.val < 16 := by
  rw [rustPatterns_eq_sourcePatterns] at live ⊢
  exact pattern_read_in_range pattern limb live

/-- The literal pattern result is exactly the non-tag portion used by one
endpoint's `compressed` value.  The row and slot are irrelevant to the
pattern loop except that the row selects the sixteen openings. -/
theorem selectedTag_add_rustPatternValueLiteral_eq_compressed
    (table : Table K) (lambda : K) (index : Fin 136) (endpoint : Endpoint) :
    (selectedTag index : K) +
        rustPatternValueLiteral (fun column => table endpoint.row column)
          lambda endpoint.pattern =
      compressed table lambda index endpoint := by
  rw [rustPatternValueLiteral_eq_sourcePatternValue]
  unfold sourcePatternValue compressed patternLimb
  rfl

#print axioms rustPatterns_eq_sourcePatterns
#print axioms rustPowerAt_eq_pow
#print axioms rustPatternValueLiteral_eq_sourcePatternValue
#print axioms rust_live_column_in_range
#print axioms selectedTag_add_rustPatternValueLiteral_eq_compressed
end AspisV8Completion.SelectedCopyPatternValuesLiteral
