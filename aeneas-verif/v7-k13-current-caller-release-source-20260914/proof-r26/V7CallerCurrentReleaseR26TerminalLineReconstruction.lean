import V7CallerCurrentReleaseR26TerminalLineClaim

/-!
# Reconstruction of terminal line coefficients from four M31 limbs

The optimized dot path stores each QM31 coefficient as four canonical base
field limbs.  Its generated closure only reads those limbs and rebuilds the
nested extension element; this theorem records that exact correspondence.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalLineReconstruction

open V7CallerCurrentReleaseR26FieldBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩

def CanonicalFourLimbs (limbs : Array RawM31 4#usize) : Prop :=
  ∀ index, index < 4 → GeneratedCanonicalM31 limbs.val[index]!

def exactQm31OfLimbs (limbs : Array RawM31 4#usize) : ExactQM31 :=
  ⟨⟨generatedM31ToExact limbs.val[0]!,
     generatedM31ToExact limbs.val[1]!⟩,
   ⟨generatedM31ToExact limbs.val[2]!,
     generatedM31ToExact limbs.val[3]!⟩⟩

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {n : Std.Usize}
    (values : Array T n) (index : Std.Usize)
    (bound : index.val < values.length) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index bound)
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

theorem generated_terminal_qm31_from_limbs_corresponds
    (limbs : Array RawM31 4#usize)
    (canonical : CanonicalFourLimbs limbs) :
    ∃ out,
      sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call
          () limbs = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = exactQm31OfLimbs limbs := by
  let l0 := limbs.val[0]!
  let l1 := limbs.val[1]!
  let l2 := limbs.val[2]!
  let l3 := limbs.val[3]!
  have read0 : Array.index_usize limbs 0#usize = ok l0 := by
    simpa [l0, Array.length_eq] using
      arrayIndexRun limbs 0#usize (by norm_num [Array.length_eq])
  have read1 : Array.index_usize limbs 1#usize = ok l1 := by
    simpa [l1, Array.length_eq] using
      arrayIndexRun limbs 1#usize (by norm_num [Array.length_eq])
  have read2 : Array.index_usize limbs 2#usize = ok l2 := by
    simpa [l2, Array.length_eq] using
      arrayIndexRun limbs 2#usize (by norm_num [Array.length_eq])
  have read3 : Array.index_usize limbs 3#usize = ok l3 := by
    simpa [l3, Array.length_eq] using
      arrayIndexRun limbs 3#usize (by norm_num [Array.length_eq])
  let out : RawQM31 := ⟨⟨l0, l1⟩, ⟨l2, l3⟩⟩
  refine ⟨out, ?_, ?_, ?_⟩
  · simp [sumcheck.WeightAccumulator.dot.closure.Insts.CoreOpsFunctionFnTupleArrayM314QM31.call,
      field.CM31.new, read0, read1, read2, read3, out]
  · exact ⟨⟨canonical 0 (by norm_num), canonical 1 (by norm_num)⟩,
      ⟨canonical 2 (by norm_num), canonical 3 (by norm_num)⟩⟩
  · rfl

#print axioms generated_terminal_qm31_from_limbs_corresponds

end V7CallerCurrentReleaseR26TerminalLineReconstruction
