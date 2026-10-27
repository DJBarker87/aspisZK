import R1Z.PV_CBL_PathJoinShape
namespace R1Z.PV_CBL_PathJoinLength
open Aeneas.Std PV_CBL_PathJoinValue
set_option autoImplicit false

theorem separator_bound (base : List U8) : (separator base).length≤1 := by
  unfold separator
  split <;> simp

theorem length (base path : List U8) :
    (join base path).length = if path.head?=some slash then path.length
      else base.length+(separator base).length+path.length := by
  by_cases h : path.head?=some slash
  · simp only [join,h,if_true]
  · simp only [join,h,if_false,List.length_append]

theorem bound (base path : List U8) :
    (join base path).length≤base.length+1+path.length := by
  rw [length]
  have := separator_bound base
  split <;> omega
#print axioms separator_bound
#print axioms length
#print axioms bound
end R1Z.PV_CBL_PathJoinLength
