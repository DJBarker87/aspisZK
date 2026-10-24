import S9ActualRawCanonicalRefinementV1
import S9ActualEbyKBackendTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualRawNativeOperandsV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9ActualRawCanonicalRefinementV1
abbrev A4 := Array U32 4#usize

def low (w : NativeW) : A4 := Array.make 4#usize
  [w.c0.c0.a,w.c0.c0.b,w.c0.c1.a,w.c0.c1.b]
def high (w : NativeW) : A4 := Array.make 4#usize
  [w.c1.c0.a,w.c1.c0.b,w.c1.c1.a,w.c1.c1.b]

theorem actual_from_wide_same_lanes (w : NativeW) :
    fast_pairing.canonical.Q.from_wide w = .ok (Array.make 2#usize [low w,high w]) := by
  rfl

/-- Bounds follow from the SAME actual scalar validation, including its
short-circuit rejection semantics. No independent scalar-canonicality premise. -/
theorem same_checked_q_bounds (scalar : NativeQ) (q : A4)
    (h : fast_pairing.checked_q scalar = .ok (.Ok q)) :
    q.val[0]!.val ≤ 2^31-2 ∧ q.val[1]!.val ≤ 2^31-2 ∧
    q.val[2]!.val ≤ 2^31-2 ∧ q.val[3]!.val ≤ 2^31-2 := by
  have hs := native_checked_q_success_to_source scalar q h
  obtain ⟨he,hall⟩ := AspisR1EbyKCheckedQConcreteAll.checkedQ_success_canonical
    (toSourceQ scalar) q hs
  subst q
  have h0 := hall scalar.c0.a (by simp [toSourceQ,Array.make])
  have h1 := hall scalar.c0.b (by simp [toSourceQ,Array.make])
  have h2 := hall scalar.c1.a (by simp [toSourceQ,Array.make])
  have h3 := hall scalar.c1.b (by simp [toSourceQ,Array.make])
  change scalar.c0.a.val ≤ 2^31-2 ∧ scalar.c0.b.val ≤ 2^31-2 ∧
    scalar.c1.a.val ≤ 2^31-2 ∧ scalar.c1.b.val ≤ 2^31-2
  omega

/-- Both raw operands produced by the actual fromWide lane split and SAME
accepted checked_q call lie in the source-refinement domain. Wide bounds are
coordinate propositions, so existing native canonical-input bounds compose
without importing or changing the retained raw mathematical field cohort. -/
theorem actual_same_operands_raw_refines (w : NativeW) (scalar : NativeQ) (q : A4)
    (hw : w.c0.c0.a.val ≤ 2^31-2 ∧ w.c0.c0.b.val ≤ 2^31-2 ∧
      w.c0.c1.a.val ≤ 2^31-2 ∧ w.c0.c1.b.val ≤ 2^31-2 ∧
      w.c1.c0.a.val ≤ 2^31-2 ∧ w.c1.c0.b.val ≤ 2^31-2 ∧
      w.c1.c1.a.val ≤ 2^31-2 ∧ w.c1.c1.b.val ≤ 2^31-2)
    (hchecked : fast_pairing.checked_q scalar = .ok (.Ok q)) :
    fast_pairing.canonical.Q.from_wide w = .ok (Array.make 2#usize [low w,high w]) ∧
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw (low w) q =
      AspisR1CanonicalQRawUnified.canonical.Q.raw (low w) q ∧
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw (high w) q =
      AspisR1CanonicalQRawUnified.canonical.Q.raw (high w) q := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := hw
  obtain ⟨q0,q1,q2,q3⟩ := same_checked_q_bounds scalar q hchecked
  refine ⟨actual_from_wide_same_lanes w,?_,?_⟩
  · exact actual_raw_eq_checked_of_canonical (low w) q h0 h1 h2 h3 q0 q1 q2 q3
  · exact actual_raw_eq_checked_of_canonical (high w) q h4 h5 h6 h7 q0 q1 q2 q3

#print axioms actual_from_wide_same_lanes
#print axioms same_checked_q_bounds
#print axioms actual_same_operands_raw_refines
end AspisR1S9ActualRawNativeOperandsV1
