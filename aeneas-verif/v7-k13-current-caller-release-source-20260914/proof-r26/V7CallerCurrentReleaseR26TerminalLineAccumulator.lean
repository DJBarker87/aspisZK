import V7CallerCurrentReleaseR26Qm31SumProducts4Semantics
import V7CallerCurrentReleaseR26Qm31DotRawArithmetic
import V7CallerCurrentReleaseR26TerminalLineReconstruction

/-!
# Optimized terminal line accumulator

This file verifies the generated line accumulator used by terminal `dot`.
The release instance has one sixteen-line batch whose deferred-halving count
already equals the global maximum, so the scale-alignment loop is an identity.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineAccumulator

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

/-- When a line already carries the maximum deferred-halving count, the
generated scale-alignment loop returns it unchanged. -/
theorem generated_line_scale_alignment_equal
    (deferred : Std.U8) (scale : RawQM31) :
    sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop0
        deferred scale deferred = ok scale := by
  simp [sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop0,
    sumcheck.WeightAccumulator.impl.accumulate_line_dot_loop0.body,
    loop, UScalar.lt_equiv]

def exactLineFactor (x : RawM31) (slot : Nat) : ExactM31 :=
  if slot = 0 then generatedM31ToExact x
  else if slot = 1 then 2 * generatedM31ToExact x ^ 2 - 1
  else generatedM31ToExact x * (2 * generatedM31ToExact x ^ 2 - 1)

def lineFactors (x high product : RawM31) : Array RawM31 3#usize :=
  Array.make 3#usize [x, high, product]

def CanonicalLineFactors (factors : Array RawM31 3#usize) : Prop :=
  ∀ slot, slot < 3 → GeneratedCanonicalM31 factors.val[slot]!

theorem generated_line_factors_correspond
    (x : RawM31) (canonical : GeneratedCanonicalM31 x) :
    ∃ high product,
      sumcheck.WeightAccumulator.impl.double_x_m31 x = ok high ∧
      field.M31.mul x high = ok product ∧
      CanonicalLineFactors (lineFactors x high product) ∧
      generatedM31ToExact high = exactLineFactor x 1 ∧
      generatedM31ToExact product = exactLineFactor x 2 := by
  obtain ⟨high, highRun, highCanonical, highExact⟩ :=
    generated_double_x_m31_corresponds x canonical
  obtain ⟨product, productRun, productCanonical, productExact⟩ :=
    generated_m31_mul_corresponds x high canonical highCanonical
  refine ⟨high, product, highRun, productRun, ?_, ?_, ?_⟩
  · intro slot slotBound
    have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals simp [lineFactors]
    all_goals assumption
  · simpa [exactLineFactor] using highExact
  · change ((product.val : Nat) : ExactM31) = _
    rw [productExact]
    have highExact' : ((high.val : Nat) : ExactM31) =
        2 * generatedM31ToExact x ^ 2 - 1 := by
      simpa [generatedM31ToExact] using highExact
    rw [highExact']
    simp [exactLineFactor, generatedM31ToExact]

def scaleLimb (scale : RawQM31) (limb : Nat) : RawM31 :=
  if limb = 0 then scale.c0.a
  else if limb = 1 then scale.c0.b
  else if limb = 2 then scale.c1.a
  else scale.c1.b

def exactScaleLimb (scale : RawQM31) (limb : Nat) : ExactM31 :=
  generatedM31ToExact (scaleLimb scale limb)

theorem canonical_scale_limb
    (scale : RawQM31) (canonical : GeneratedCanonicalQM31 scale)
    (limb : Nat) (limbBound : limb < 4) :
    GeneratedCanonicalM31 (scaleLimb scale limb) := by
  rcases canonical with ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
  have cases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [scaleLimb] <;> assumption

#print axioms generated_line_scale_alignment_equal
#print axioms generated_line_factors_correspond
#print axioms canonical_scale_limb

end V7CallerCurrentReleaseR26TerminalLineAccumulator
