import R1Z.PV_RunJoin_ByteSlice40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteRead40
open Aeneas Aeneas.Std Result

theorem read (s : Slice U8) (i : Usize) (h : i.val<s.length) :
    Slice.index_usize s i=.ok (s.val[i.val]'h) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,List.getElem?_eq_getElem h]
theorem zero (s : Slice U8) (i : Usize) (h : i.val<s.length)
    (hz : s.val[i.val]?=some 0#u8) : Slice.index_usize s i=.ok 0#u8 := by
  rw [read s i h]
  have he : s.val[i.val]'h=0#u8 := by
    simpa only [List.getElem?_eq_getElem h,Option.some.injEq] using hz
  rw [he]
#print axioms read
#print axioms zero
end R1Z.PV_RunJoin_ByteRead40
