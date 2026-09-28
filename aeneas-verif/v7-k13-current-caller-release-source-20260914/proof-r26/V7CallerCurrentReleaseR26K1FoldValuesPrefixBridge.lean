import V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
import V7CallerCurrentReleaseR26K1QueryWeightBridge

/-!
# Current value-prefix folds in the maintained K1 field

This file transports the exact source-array result through the explicit R26
to K1 field isomorphism and identifies it with K1's maintained natural
coefficient fold.  The three live relation-tail sizes are direct corollaries
of one generic theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26FoldValuesPrefixSemantics
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open AspisV5ComponentCConcreteFoldLinearity

abbrev RawQM31 := field.QM31
abbrev SourceQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

/-- The K1 view of any typed prefix of the source's 256-entry backing array. -/
def modelPrefix (values : Array RawQM31 256#usize) (length : Nat) :
    Fin length → ModelQM31 :=
  fun index => sourceQm31ToModel (exactValueAt values index.val)

/-- One source fibre, after field transport, is definitionally the same
fibre-major natural fold used by K1. -/
theorem coefficientFoldAt_model_eq_layer
    (values : Array RawQM31 256#usize) (alpha : SourceQM31)
    (n : Nat) (fibre : Fin n) :
    sourceQm31ToModel (coefficientFoldAt values alpha fibre.val) =
      coefficientFoldLayer n (sourceQm31ToModel alpha)
        (modelPrefix values (4 * n)) fibre := by
  rw [coefficientFoldLayer_apply]
  unfold coefficientFoldValue coefficientFoldAt modelPrefix exactValueAt
  simp only [sourceQm31ToModel_add, sourceQm31ToModel_mul]
  change
    sourceQm31ToModelHom
        (generatedQm31ToExact values.val[4 * fibre.val]! +
          alpha * generatedQm31ToExact values.val[4 * fibre.val + 1]! +
          alpha ^ 2 * generatedQm31ToExact values.val[4 * fibre.val + 2]! +
          alpha ^ 3 * generatedQm31ToExact values.val[4 * fibre.val + 3]!) = _
  simp only [map_add, map_mul, map_pow, sourceQm31ToModelHom_apply]
  rfl

/-- Generic current-source/K1 bridge for one successful in-place prefix
fold.  It also retains canonicality and the unchanged backing-array suffix
needed to chain the three production calls. -/
theorem fold_values_prefix_equals_model_layer
    (input : Std.Usize) (values output : Array RawQM31 256#usize)
    (alpha : RawQM31) (n : Nat)
    (hinput : input.val = 4 * n)
    (hn : n ≤ 64)
    (hvalues : CanonicalValues values)
    (halpha : GeneratedCanonicalQM31 alpha)
    (run : v6_transcript.fold_values_prefix input values alpha = ok output) :
    CanonicalValues output ∧
      (∀ fibre : Fin n,
        sourceQm31ToModel (exactValueAt output fibre.val) =
          coefficientFoldLayer n
            (sourceQm31ToModel (generatedQm31ToExact alpha))
            (modelPrefix values (4 * n)) fibre) ∧
      ∀ index, n ≤ index → index < 256 →
        output.val[index]! = values.val[index]! := by
  obtain ⟨outputCanonical, outputExact, outputSuffix⟩ :=
    fold_values_prefix_exact input values output alpha n hinput hn hvalues
      halpha run
  refine ⟨outputCanonical, ?_, outputSuffix⟩
  intro fibre
  rw [outputExact fibre.val fibre.isLt]
  exact coefficientFoldAt_model_eq_layer values
    (generatedQm31ToExact alpha) n fibre

/-- Live round one: the 256-entry disclosed vector becomes 64 K1 values. -/
theorem fold_values_prefix_256_equals_model_layer
    (values output : Array RawQM31 256#usize) (alpha : RawQM31)
    (hvalues : CanonicalValues values)
    (halpha : GeneratedCanonicalQM31 alpha)
    (run : v6_transcript.fold_values_prefix 256#usize values alpha = ok output) :
    CanonicalValues output ∧
      ∀ fibre : Fin 64,
        sourceQm31ToModel (exactValueAt output fibre.val) =
          coefficientFoldLayer 64
            (sourceQm31ToModel (generatedQm31ToExact alpha))
            (modelPrefix values 256) fibre := by
  obtain ⟨canonical, exact, _⟩ :=
    fold_values_prefix_equals_model_layer 256#usize values output alpha 64
      (by norm_num) (by norm_num) hvalues halpha run
  exact ⟨canonical, by simpa using exact⟩

/-- Live round two: the first 64 entries become 16 K1 values. -/
theorem fold_values_prefix_64_equals_model_layer
    (values output : Array RawQM31 256#usize) (alpha : RawQM31)
    (hvalues : CanonicalValues values)
    (halpha : GeneratedCanonicalQM31 alpha)
    (run : v6_transcript.fold_values_prefix 64#usize values alpha = ok output) :
    CanonicalValues output ∧
      ∀ fibre : Fin 16,
        sourceQm31ToModel (exactValueAt output fibre.val) =
          coefficientFoldLayer 16
            (sourceQm31ToModel (generatedQm31ToExact alpha))
            (modelPrefix values 64) fibre := by
  obtain ⟨canonical, exact, _⟩ :=
    fold_values_prefix_equals_model_layer 64#usize values output alpha 16
      (by norm_num) (by norm_num) hvalues halpha run
  exact ⟨canonical, by simpa using exact⟩

/-- Live round three: the first 16 entries become the final four K1 values. -/
theorem fold_values_prefix_16_equals_model_layer
    (values output : Array RawQM31 256#usize) (alpha : RawQM31)
    (hvalues : CanonicalValues values)
    (halpha : GeneratedCanonicalQM31 alpha)
    (run : v6_transcript.fold_values_prefix 16#usize values alpha = ok output) :
    CanonicalValues output ∧
      ∀ fibre : Fin 4,
        sourceQm31ToModel (exactValueAt output fibre.val) =
          coefficientFoldLayer 4
            (sourceQm31ToModel (generatedQm31ToExact alpha))
            (modelPrefix values 16) fibre := by
  obtain ⟨canonical, exact, _⟩ :=
    fold_values_prefix_equals_model_layer 16#usize values output alpha 4
      (by norm_num) (by norm_num) hvalues halpha run
  exact ⟨canonical, by simpa using exact⟩

#print axioms coefficientFoldAt_model_eq_layer
#print axioms fold_values_prefix_equals_model_layer
#print axioms fold_values_prefix_256_equals_model_layer
#print axioms fold_values_prefix_64_equals_model_layer
#print axioms fold_values_prefix_16_equals_model_layer

end V7CallerCurrentReleaseR26K1FoldValuesPrefixBridge
