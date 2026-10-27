import Aeneas.Std
import RPv_ExtractedMaskQmPackBase4Array

/-! Exact copy prelude parameterized by the source's explicit initializer.
This avoids identifying a typeclass default with the generated `QM31.ZERO`. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4InitCopy

open Aeneas.Std Result

def copyPrefixWith {α : Type} (init : α) (copyInst : core.marker.Copy α)
    (values : Slice α) : Result (Array α 4#usize) := do
  let padded := Array.repeat 4#usize init
  let i1 := Slice.len values
  let (s, back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice α)) padded
      { «end» := i1 }
  let s1 ← core.slice.Slice.copy_from_slice copyInst s values
  let padded1 := back s1
  ok padded1

theorem copyPrefixWith_eq_source {α : Type} (init : α)
    (copyInst : core.marker.Copy α) (values : Slice α)
    (hlen : values.length = 4) :
    ∃ out : Array α 4#usize,
      copyPrefixWith init copyInst values = .ok out ∧ out.val = values.val := by
  let padded : Array α 4#usize := Array.repeat 4#usize init
  let r : core.ops.range.RangeTo Usize := { «end» := Slice.len values }
  have hr : r.end.val = 4 := by simp [r, Slice.len_val, hlen]
  have hmut := Array.index_mut_SliceIndexRangeToUsizeSlice padded r (by
    simp [r, hr])
  obtain ⟨pair, hrun, hpost⟩ := WP.spec_imp_exists hmut
  rcases pair with ⟨s, back⟩
  have hslen : s.length = 4 := by simpa [hr] using hpost.2.1
  have hcopywp := core.slice.Slice.copy_from_slice.step_spec
    copyInst s values (by rw [hslen, hlen])
  obtain ⟨s1, hcopy, hs1⟩ := WP.spec_imp_exists hcopywp
  have hval : (back s1).val = values.val := by
    rw [hs1]
    have hback := hpost.2.2 values
    rw [hback]
    exact AspisR1.Qm31PackBase4SliceFacts.setSlice_zero_eq_source
      padded.val values.val (by simpa [padded] using padded.property) hlen
  refine ⟨back s1, ?_, hval⟩
  simp [copyPrefixWith, padded, r, hrun, hcopy, hs1, bind_tc_ok]

#print axioms copyPrefixWith_eq_source
end AspisR1.ExtractedMaskQmPackBase4InitCopy
