import NGD_AtDomains
import NGO_ParseDomain
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_AtDomain
open AspisR1PrefixAggregateParser
/-- The caller's borrowed framed record has exactly the original source
window and header-imposed size, for arbitrary full child behavior. -/
theorem from_source_window (bytes framed : Slice U8) (offset finish size : Usize)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=offset,«end»:=finish}=ok (some framed))
    (addition : finish.val=offset.val+5+size.val) :
    framed.val.length=5+size.val ∧
      framed.val=(bytes.val.drop offset.val).take (5+size.val) := by
  simp only [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.get] at get
  split at get
  next fitting =>
    have equal:=Option.some.inj (Result.ok.inj get)
    have values:=congrArg Subtype.val equal
    simp only [List.slice] at values
    have fitEnd : finish.val≤bytes.val.length := fitting.2
    have exactWindow : framed.val=(bytes.val.drop offset.val).take (5+size.val) := by
      rw [←values]
      congr 1
      omega
    refine ⟨?_,exactWindow⟩
    rw [exactWindow,List.length_take,List.length_drop]
    omega
  next failed => cases get
#print axioms from_source_window
end NGO_AtDomain
