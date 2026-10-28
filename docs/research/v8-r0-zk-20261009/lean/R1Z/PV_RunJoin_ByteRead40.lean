import R1Z.PV_RunJoin_ByteSlice40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteRead40
open Aeneas Aeneas.Std Result

theorem read (s : Slice U8) (i : Usize) (h : i.val<s.length) :
    Slice.index_usize s i=.ok (s.val[i.val]'h) := by
  simp only [Slice.index_usize,h,↓reduceDIte]
#print axioms read
end R1Z.PV_RunJoin_ByteRead40
