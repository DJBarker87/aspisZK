import XRk_Funs
open Aeneas Aeneas.Std Result
namespace XRl_GeometryInput
/-- A successful actual array range read derives both its own bounds and its
exact span, rather than importing a caller-selected length witness. -/
theorem range {T : Type} {N : Usize} (a : Array T N) (start finish : Usize) (out : Slice T)
    (run : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice T))
      a ⟨start,finish⟩=ok out) :
    start.val≤finish.val ∧ finish.val≤a.val.length ∧ out.val.length=finish.val-start.val := by
  simp only [Array.index_SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.index] at run
  split at run
  · rename_i bound
    have same := Result.ok.inj run
    have content := congrArg (fun s : Slice T => s.val) same
    subst out
    change start.val≤finish.val ∧ finish.val≤a.val.length at bound
    refine ⟨bound.1,bound.2,?_⟩
    simp only [List.slice,List.length_take,List.length_drop]
    omega
  · cases run
#print axioms range
end XRl_GeometryInput
