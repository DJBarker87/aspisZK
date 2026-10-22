import S8Kani2CallerJoin

/-! Exact list-valued finish target. This module removes existential output
choices and needs neither raw bounds nor a successful-value hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace S8JoinFinishExact
open Aeneas Aeneas.Std Result
open S8OwnedP6ValueModel S8OwnedP6Finish
open S8Kani2FinishReferenceJoin S8Kani2MutableValue
open S8Kani2MutableExtraction.batched_weights

/-- Complete reference output, truncated to the actual destination length. -/
def output (raw : Raw) (old : Weights) : Weights :=
  ⟨(raw.val.take old.length).map modelValue, by
    simp only [List.length_map, List.length_take]
    exact (Nat.min_le_right _ _).trans old.property⟩

theorem reference_exact (raw : Raw) (old : Weights)
    (lengths : old.length ≤ raw.length) :
    S8OwnedP6.finish_owned raw old = .ok (output raw old) := by
  obtain ⟨out, run, len, cells⟩ := finish_total_model raw old lengths
  have same : out = output raw old := by
    apply Subtype.ext
    apply List.ext_getElem?
    intro j
    by_cases hj : j < old.length
    · simpa [output, List.getElem?_take, hj] using cells j hj
    · have ho : out.val[j]? = none := List.getElem?_eq_none (by omega)
      rw [ho]
      symm
      apply List.getElem?_eq_none
      simp only [output, List.length_map, List.length_take]
      omega
  simpa only [same] using run

/-- Whole mutable traversal returns exactly the transported reference list. -/
theorem mutable_exact (raw : Raw) (old : Weights) (terms : Usize)
    (lengths : old.length ≤ raw.length) :
    ∃ out : FinishSlice,
      BatchedWeights.finish (⟨raw,terms⟩ : F.BW) (toSlice old) = .ok out ∧
      out.val = (output raw old).val.map toFinish := by
  obtain ⟨out, run, shape, cells⟩ :=
    S8Kani2FinishCertificate.mutable_finish_total (⟨raw,terms⟩ : F.BW) (toSlice old)
      (by simpa [toSlice] using lengths)
  refine ⟨out,run,?_⟩
  have len : out.val.length = old.length := by
    rw [shape]
    simp [S8Kani2MutableOutput.prefixWrite, S8Kani2PendingWrite.prefixWrite,
      toSlice]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < old.length
  · let i : Usize := ⟨j,by have := old.property; omega⟩
    obtain ⟨refOut,sourceOut,href,_,hsource,hcell⟩ :=
      finish_reference_simulation raw old terms lengths
    have same : sourceOut = out := Result.ok.inj (hsource.symm.trans run)
    obtain ⟨row,hrow,_,hread⟩ := hcell i hj
    rw [same] at hread
    have index := WP.spec_imp_exists (Slice.index_usize_spec out i (by simpa [len] using hj))
    obtain ⟨q,hq,hqval⟩ := index
    have eq := Result.ok.inj (hq.symm.trans hread)
    rw [← eq] at hqval
    simp only [output,List.getElem?_map,List.getElem?_take,if_pos hj,hrow,Option.map_some]
    rw [List.getElem?_eq_getElem (by omega)]
    exact congrArg some hqval.symm
  · rw [List.getElem?_eq_none (by omega)]
    symm
    apply List.getElem?_eq_none
    simp only [output,List.length_map,List.length_take]
    omega

#print axioms reference_exact
#print axioms mutable_exact
end S8JoinFinishExact
