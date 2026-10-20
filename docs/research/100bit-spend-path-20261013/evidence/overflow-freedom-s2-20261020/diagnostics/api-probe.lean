import R22Stage2LocalBodies
open Aeneas Aeneas.Std Result
#synth HAdd Usize Usize (Result Usize)
#synth HMul Usize Usize (Result Usize)
#synth HShiftLeft Usize U32 (Result Usize)
#print UScalar.add
#print UScalar.shiftLeft
#check core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
#check Slice.index_SliceIndexRangeUsizeSliceInst
set_option pp.all true in
#print AspisR1Stage2.compact.OPENING
#print instHAddUScalarResult
#check UScalar.add_spec
example : (480#usize + 128#usize : Result Usize) = ok 608#usize := by
  change UScalar.tryMk _ (480+128) = ok _
  simp (disch := scalar_tac) [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, Result.ofOption]
