import V7CallerCurrentReleaseR26Qm31DotRawOuterBody

/-!
# Four-input raw chunk invariant

Each raw chunk contains at most four products per lane.  The invariant below
turns that count into the headroom premise used by the verified outer body.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawChunkLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26Qm31DotRawInnerLoop
open V7CallerCurrentReleaseR26Qm31DotRawOuterBody

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev Pair := CM31 × CM31
abbrev Raw := Array Std.U64 9#usize

local instance : Inhabited Std.U64 := ⟨0#u64⟩
local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩

def RawComponentCountBound (raw : Raw) (processed : Nat) : Prop :=
  ∀ component, component < 3 →
    raw.val[component * 3]!.val ≤ processed * 2 ^ 62 ∧
      raw.val[component * 3 + 1]!.val ≤ processed * 2 ^ 62 ∧
      raw.val[component * 3 + 2]!.val ≤ processed * 2 ^ 62

theorem raw_component_count_bound_headroom
    (raw : Raw) (processed : Nat)
    (processedBound : processed < 4)
    (bound : RawComponentCountBound raw processed) :
    RawUniversalHeadroom raw := by
  intro lane laneBound left right leftCanonical rightCanonical
  have productBound := canonical_m31_product_lt_two_pow_62 left right
    leftCanonical rightCanonical
  have laneCases : lane = 0 ∨ lane = 1 ∨ lane = 2 ∨ lane = 3 ∨
      lane = 4 ∨ lane = 5 ∨ lane = 6 ∨ lane = 7 ∨ lane = 8 := by
    omega
  rcases laneCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have current := (bound 0 (by omega)).1
    norm_num at current ⊢
    omega
  · have current := (bound 0 (by omega)).2.1
    norm_num at current ⊢
    omega
  · have current := (bound 0 (by omega)).2.2
    norm_num at current ⊢
    omega
  · have current := (bound 1 (by omega)).1
    norm_num at current ⊢
    omega
  · have current := (bound 1 (by omega)).2.1
    norm_num at current ⊢
    omega
  · have current := (bound 1 (by omega)).2.2
    norm_num at current ⊢
    omega
  · have current := (bound 2 (by omega)).1
    norm_num at current ⊢
    omega
  · have current := (bound 2 (by omega)).2.1
    norm_num at current ⊢
    omega
  · have current := (bound 2 (by omega)).2.2
    norm_num at current ⊢
    omega

theorem natural_component_steps_advance_count_bound
    (before after : Raw) (processed : Nat) (pairs : Array Pair 3#usize)
    (beforeBound : RawComponentCountBound before processed)
    (pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2)
    (steps : ∀ component, component < 3 →
      NaturalRawComponentStep before after component pairs.val[component]!) :
    RawComponentCountBound after (processed + 1) := by
  intro component componentBound
  have prior := beforeBound component componentBound
  have canonical := pairsCanonical component componentBound
  have step := steps component componentBound
  have product0 := canonical_m31_product_lt_two_pow_62
    pairs.val[component]!.1.a pairs.val[component]!.2.a
      canonical.1.1 canonical.2.1
  have product1 := canonical_m31_product_lt_two_pow_62
    pairs.val[component]!.1.b pairs.val[component]!.2.b
      canonical.1.2 canonical.2.2
  have leftSumSpec := canonicalM31Sum_spec pairs.val[component]!.1.a
    pairs.val[component]!.1.b canonical.1.1 canonical.1.2
  have rightSumSpec := canonicalM31Sum_spec pairs.val[component]!.2.a
    pairs.val[component]!.2.b canonical.2.1 canonical.2.2
  have product2 := canonical_m31_product_lt_two_pow_62
    (canonicalM31Sum pairs.val[component]!.1.a
      pairs.val[component]!.1.b)
    (canonicalM31Sum pairs.val[component]!.2.a
      pairs.val[component]!.2.b)
    leftSumSpec.2.1 rightSumSpec.2.1
  unfold NaturalRawComponentStep at step
  refine ⟨?_, ?_, ?_⟩
  · rw [step.1]
    omega
  · rw [step.2.1]
    omega
  · rw [step.2.2]
    omega

#print axioms raw_component_count_bound_headroom
#print axioms natural_component_steps_advance_count_bound

end V7CallerCurrentReleaseR26Qm31DotRawChunkLoop
