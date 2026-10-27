import R1Z.PV_CBL_PaddingModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingCount
open PV_CBL_PaddingModel
set_option autoImplicit false
theorem one (buffer suffix : List U8) (pos : Nat) (h : pos<56) :
    blocks buffer pos suffix = [first buffer pos suffix] := by simp [blocks,second,h]
theorem two (buffer suffix : List U8) (pos : Nat) (h : 56≤pos) :
    blocks buffer pos suffix = [first buffer pos suffix,List.replicate 56 0#u8 ++ suffix] := by
  simp [blocks,second,show ¬pos<56 by omega]
theorem count (buffer suffix : List U8) (pos : Nat) :
    (blocks buffer pos suffix).length = if pos<56 then 1 else 2 := by
  by_cases h : pos<56
  · simp [one buffer suffix pos h,h]
  · simp [two buffer suffix pos (by omega),h]
#print axioms one
#print axioms two
#print axioms count
end R1Z.PV_CBL_PaddingCount
