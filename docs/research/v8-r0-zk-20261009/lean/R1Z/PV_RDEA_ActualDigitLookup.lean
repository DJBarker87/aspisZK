import R1Z.PV_RDEA_ActualDigitTable
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEA_ActualDigitLookup
open PV_RDEA_ActualDigitTable

theorem index_length (i : Usize) (s : Str) (h : Array.index_usize table i=.ok s) : s.val.length=1 := by
  unfold Array.index_usize at h
  split at h
  · cases h
  · rename_i x hx
    cases h
    change table.val[i.val]?=some x at hx
    obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp hx
    have hb : i.val<16 := by simpa only [table,Array.make,List.length_cons,List.length_nil] using bound
    rw [←eq]
    exact entry_length ⟨i.val,hb⟩

#print axioms index_length
end R1Z.PV_RDEA_ActualDigitLookup
