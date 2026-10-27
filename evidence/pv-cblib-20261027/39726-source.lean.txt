import R1Z.PV_CBL_PathJoinValue
namespace R1Z.PV_CBL_PathJoinSuffix
open Aeneas.Std PV_CBL_PathJoinValue
set_option autoImplicit false

theorem suffix (base path : List U8) : ∃ prefixBytes, join base path=prefixBytes++path := by
  unfold join
  split
  · exact ⟨[],rfl⟩
  · exact ⟨base++separator base,rfl⟩

#print axioms suffix
end R1Z.PV_CBL_PathJoinSuffix
