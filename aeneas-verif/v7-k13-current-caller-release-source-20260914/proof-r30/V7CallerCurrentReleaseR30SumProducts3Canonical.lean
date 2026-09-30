import V7CallerCurrentReleaseR26PreparedSum3Semantics

/-!
# Canonical output of the three-term QM31 sum-product

The delayed channel-accumulation loop may produce any nine U64 channel sums,
but the final Karatsuba reconstruction reduces them into canonical QM31
limbs.  This theorem isolates exactly that consequence for the generated
three-term wrapper.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30SumProducts3Canonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26PreparedSum3Semantics

abbrev RawQM31 := field.QM31

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

theorem successful_qm31_sum_products3_canonical
    (left right : Array RawQM31 3#usize) (out : RawQM31)
    (run : field.qm31_sum_products3 left right = ok out) :
    GeneratedCanonicalQM31 out := by
  unfold field.qm31_sum_products3 field.qm31_sum_products_small at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sums, loopRun, reconstructionRun⟩ := run
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_reconstruction_corresponds sums
  have outputExact : out = expected :=
    Result.ok.inj (reconstructionRun.symm.trans expectedRun)
  rw [outputExact]
  exact expectedCanonical

#print axioms successful_qm31_sum_products3_canonical

end V7CallerCurrentReleaseR30SumProducts3Canonical
