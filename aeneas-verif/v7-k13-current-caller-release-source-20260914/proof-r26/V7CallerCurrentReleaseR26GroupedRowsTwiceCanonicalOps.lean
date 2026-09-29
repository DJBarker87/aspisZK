import V7CallerCurrentReleaseR26GroupedRowsTwiceChunkOutput
import V7CallerCurrentReleaseR26HalfBridge

/-!
# Canonical raw operations for the fused grouped-fold proof

This packages the existing source-to-exact field bridges as total operations
on canonical generated QM31 values.  It lets the four fixed chunk traces be
constructed symbolically while retaining both their source executions and
their exact-field meanings.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26HalfBridge

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

structure CanonicalRaw where
  raw : RawQM31
  canonical : GeneratedCanonicalQM31 raw

def exact (value : CanonicalRaw) : ExactQM31 :=
  generatedQm31ToExact value.raw

def zero : CanonicalRaw :=
  ⟨field.QM31.ZERO, generated_qm31_zero_canonical⟩

theorem oneCanonical : GeneratedCanonicalQM31 field.QM31.ONE := by
  simp only [GeneratedCanonicalQM31, GeneratedCanonicalCM31, field.QM31.ONE]
  repeat' constructor <;> norm_num

def one : CanonicalRaw := ⟨field.QM31.ONE, oneCanonical⟩

noncomputable def add (left right : CanonicalRaw) : CanonicalRaw := by
  let witness := Classical.choose
    (generated_qm31_add_corresponds left.raw right.raw
      left.canonical right.canonical)
  exact ⟨witness, (Classical.choose_spec
    (generated_qm31_add_corresponds left.raw right.raw
      left.canonical right.canonical)).2.1⟩

theorem add_run (left right : CanonicalRaw) :
    field.QM31.add left.raw right.raw = ok (add left right).raw := by
  exact (Classical.choose_spec
    (generated_qm31_add_corresponds left.raw right.raw
      left.canonical right.canonical)).1

theorem add_exact (left right : CanonicalRaw) :
    exact (add left right) = exact left + exact right := by
  exact (Classical.choose_spec
    (generated_qm31_add_corresponds left.raw right.raw
      left.canonical right.canonical)).2.2

noncomputable def mul (left right : CanonicalRaw) : CanonicalRaw := by
  let witness := Classical.choose
    (generated_qm31_mul_corresponds left.raw right.raw
      left.canonical right.canonical)
  exact ⟨witness, (Classical.choose_spec
    (generated_qm31_mul_corresponds left.raw right.raw
      left.canonical right.canonical)).2.1⟩

theorem mul_run (left right : CanonicalRaw) :
    field.QM31.mul left.raw right.raw = ok (mul left right).raw := by
  exact (Classical.choose_spec
    (generated_qm31_mul_corresponds left.raw right.raw
      left.canonical right.canonical)).1

theorem mul_exact (left right : CanonicalRaw) :
    exact (mul left right) = exact left * exact right := by
  exact (Classical.choose_spec
    (generated_qm31_mul_corresponds left.raw right.raw
      left.canonical right.canonical)).2.2

noncomputable def half (value : CanonicalRaw) : CanonicalRaw := by
  let witness := Classical.choose
    (generated_qm31_half_corresponds value.raw value.canonical)
  exact ⟨witness, (Classical.choose_spec
    (generated_qm31_half_corresponds value.raw value.canonical)).2.1⟩

theorem half_run (value : CanonicalRaw) :
    field.QM31.half value.raw = ok (half value).raw := by
  exact (Classical.choose_spec
    (generated_qm31_half_corresponds value.raw value.canonical)).1

theorem half_exact (value : CanonicalRaw) :
    exact (half value) + exact (half value) = exact value := by
  exact (Classical.choose_spec
    (generated_qm31_half_corresponds value.raw value.canonical)).2.2

theorem exact_zero : exact zero = 0 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [exact, zero, generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [exact, zero, generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ZERO]

theorem exact_one : exact one = 1 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      norm_num [exact, one, generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ONE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply QuadraticAlgebra.ext <;>
      norm_num [exact, one, generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ONE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

#print axioms add_run
#print axioms add_exact
#print axioms mul_run
#print axioms mul_exact
#print axioms half_run
#print axioms half_exact

end V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps
