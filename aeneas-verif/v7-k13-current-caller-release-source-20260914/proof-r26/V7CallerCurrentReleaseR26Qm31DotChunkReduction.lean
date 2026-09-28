import V7CallerCurrentReleaseR26Qm31DotRawChunkLoop
import V7CallerCurrentReleaseR26Qm31DotReductionLoop

/-!
# Exact reduction of one four-input QM31-dot chunk
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotChunkReduction

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotReconstruction
open V7CallerCurrentReleaseR26Qm31DotReductionLoop
open V7CallerCurrentReleaseR26Qm31DotRawChunkLoop
open V7CallerCurrentReleaseR26Qm31DotRawOuterBody

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev Pair := CM31 × CM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited M31 := ⟨field.M31.ZERO⟩
local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩
local instance : Inhabited QM31 := ⟨field.QM31.ZERO⟩

def ReducedChunkPrefix
    (weights values : Slice QM31) (start : Nat)
    (base out : Array M31 9#usize) : Prop :=
  CanonicalDotChannels out ∧
    ∀ component, component < 3 →
      let pairAt := fun offset =>
        (generatedInputPairs weights.val[start + offset]!
          values.val[start + offset]!).val[component]!
      generatedM31ToExact out.val[component * 3]! =
          generatedM31ToExact base.val[component * 3]! +
            ∑ offset ∈ Finset.range 4, exactPairLane0 (pairAt offset) ∧
        generatedM31ToExact out.val[component * 3 + 1]! =
          generatedM31ToExact base.val[component * 3 + 1]! +
            ∑ offset ∈ Finset.range 4, exactPairLane1 (pairAt offset) ∧
        generatedM31ToExact out.val[component * 3 + 2]! =
          generatedM31ToExact base.val[component * 3 + 2]! +
            ∑ offset ∈ Finset.range 4, exactPairLane2 (pairAt offset)

theorem generated_four_input_chunk_reduces
    (weights values : Slice QM31)
    (iter : core.ops.range.Range Std.Usize) (start : Nat)
    (startExact : iter.start.val = start)
    (endExact : iter.end.val = start + 4)
    (weightLength : start + 4 ≤ weights.length)
    (valueLength : start + 4 ≤ values.length)
    (weightsCanonical : ∀ offset, offset < 4 →
      GeneratedCanonicalQM31 weights.val[start + offset]!)
    (valuesCanonical : ∀ offset, offset < 4 →
      GeneratedCanonicalQM31 values.val[start + offset]!)
    (base : Array M31 9#usize)
    (baseCanonical : CanonicalDotChannels base) :
    (do
      let raw ← field.qm31_dot_loop0_loop0 iter weights values
        (Array.repeat 9#usize 0#u64)
      field.qm31_dot_loop0_loop1
        { start := 0#usize, «end» := 9#usize } base raw)
      ⦃ out => ReducedChunkPrefix weights values start base out ⦄ := by
  have rawSpec := generated_raw_chunk_loop_four weights values iter
    (Array.repeat 9#usize 0#u64) start startExact endExact weightLength
    valueLength weightsCanonical valuesCanonical
    (zero_raw_chunk_initial weights values start)
  obtain ⟨raw, rawRun, rawInvariant⟩ :=
    Aeneas.Std.WP.spec_imp_exists rawSpec
  rw [rawRun]
  simp only [bind_tc_ok]
  have reducedSpec := generated_dot_reduction_all_channels base raw baseCanonical
  obtain ⟨out, outRun, outExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists reducedSpec
  rw [outRun]
  simp only [Aeneas.Std.WP.spec_ok]
  unfold ReducedChunkPrefix
  constructor
  · exact outExact.1
  · intro component componentBound
    have rawExact := rawInvariant.1 component componentBound
    dsimp only at rawExact ⊢
    have reduced0 := outExact.2 (component * 3) (by omega)
    have reduced1 := outExact.2 (component * 3 + 1) (by omega)
    have reduced2 := outExact.2 (component * 3 + 2) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [reduced0, rawExact.1]
    · rw [reduced1, rawExact.2.1]
    · rw [reduced2, rawExact.2.2]

#print axioms generated_four_input_chunk_reduces

end V7CallerCurrentReleaseR26Qm31DotChunkReduction
