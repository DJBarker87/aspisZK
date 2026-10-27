import SAG_DotDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_DotWeights
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem read_getD {T : Type} (xs : Slice T) (index : Usize) (value fallback : T)
    (read : Slice.index_usize xs index = ok value) :
    (xs.val[index.val]?).getD fallback = value := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq] at read
  cases h : xs.val[index.val]? with
  | none => simp only [h] at read; cases read
  | some actual =>
    simp only [h] at read
    have same := Result.ok.inj read
    simp only [h,Option.getD_some,same]

theorem accumulator_read (a : verifier.Accumulator) (index : Usize)
    (value : K) (bound : index.val < 64)
    (read : Slice.index_usize a.weights.deref index = ok value) :
    AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded (SAG_DotAdapter.toFinishQ value) =
      (CheckpointBytes5Output.accumulator a).weights ⟨index.val,bound⟩ := by
  rw [←SAG_DotDecode.q_decode]
  change CheckpointBytes5Output.ofK value = CheckpointBytes5Output.ofK
    ((a.weights.val[index.val]?).getD (CheckpointBytes4ReaderFields.sourceK 0))
  have raw := read_getD a.weights.deref index value (CheckpointBytes4ReaderFields.sourceK 0) read
  exact congrArg CheckpointBytes5Output.ofK raw.symm

#print axioms read_getD
#print axioms accumulator_read
end AspisR1.SAG_DotWeights
end
