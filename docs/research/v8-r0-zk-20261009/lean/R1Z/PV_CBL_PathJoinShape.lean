import R1Z.PV_CBL_PathJoinValue
namespace R1Z.PV_CBL_PathJoinShape
open Aeneas.Std PV_CBL_PathJoinValue
set_option autoImplicit false

theorem absolute (base path : List U8) (h : path.head?=some slash) : join base path=path := by
  simp only [join,h,if_true]

theorem relative (base path : List U8) (h : path.head?≠some slash) :
    join base path=base++separator base++path := by simp only [join,h,if_false]

theorem empty_base (path : List U8) : join [] path=path := by
  unfold join
  split <;> simp [separator]

theorem trailing_slash (base : List U8) (h : base.getLast?=some slash) : separator base=[] := by
  simp only [separator,h,or_true,if_true]
#print axioms absolute
#print axioms relative
#print axioms empty_base
#print axioms trailing_slash
end R1Z.PV_CBL_PathJoinShape
