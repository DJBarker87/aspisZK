import FIw_PackArithmetic
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PackValue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_NativeValue (K Canon decode)

theorem value (a : Array NQ 4#usize) (out : NQ)
    (hc : ∀ x∈a.val,Canon x) (run : FIw_PackArithmetic.afterArray a=ok out) :
    Canon out ∧ decode out=ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
      (fun j=>qm (FIw_ArrayValue.cells a j)) := by
  let pa := FIw_PackArithmetic.array a
  let s := Array.to_slice pa
  have len : s.length=4 := by exact pa.property
  have eq := ExtractedMaskQmPackBase4Whole.after_eq_run pa s rfl len
  have inputs : ExtractedMaskQmPackBase4Whole.inputAt s len=
      (fun j=>qm (FIw_ArrayValue.cells a j)) := by
    funext j
    simp only [ExtractedMaskQmPackBase4Whole.inputAt,s,pa,FIw_PackArithmetic.array,
      FIw_ArrayValue.cells,Array.to_slice,List.getElem_map]
  have can : ∀ j : Fin 4,ExtractedMaskQM31Exact.CurrentCanonicalQM
      (ExtractedMaskQmPackBase4Whole.inputAt s len j) := by
    intro j
    rw [inputs]
    change Canon (FIw_ArrayValue.cells a j)
    exact hc _ (List.getElem_mem _)
  obtain ⟨z,hz,hcanon,hvalue⟩ := ExtractedMaskQmPackBase4Fragments.run_success
    (ExtractedMaskQmPackBase4Whole.inputAt s len) can
  have same := FIw_PackArithmetic.mapped a
  rw [run,FIv_Map.map_ok] at same
  change ok (qm out)=ExtractedMaskQmPackBase4Whole.afterArray pa at same
  rw [eq,hz] at same
  have e := Result.ok.inj same
  rw [← e] at hcanon hvalue
  rw [inputs] at hvalue
  exact ⟨hcanon,hvalue⟩
#print axioms value
end AspisR1.FIw_PackValue
end
