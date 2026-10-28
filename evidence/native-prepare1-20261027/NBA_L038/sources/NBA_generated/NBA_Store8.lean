import NBA_ArrayEight
set_option autoImplicit false
namespace AspisR1.NBA_Store8
open Aeneas Aeneas.Std Result
variable {α : Type}
def s0 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [z,z,z,z,z,z,z,z]
def s1 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,z,z,z,z,z,z,z]
def s2 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,z,z,z,z,z,z]
def s3 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,x2,z,z,z,z,z]
def s4 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,x2,x3,z,z,z,z]
def s5 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,x2,x3,x4,z,z,z]
def s6 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,x2,x3,x4,x5,z,z]
def s7 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,x2,x3,x4,x5,x6,z]
def s8 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array α 8#usize := Array.make 8#usize [x0,x1,x2,x3,x4,x5,x6,x7]
def back (z x0 x1 x2 x3 x4 x5 x6 x7 : α) (x : α) : Array α 8#usize := Array.make 8#usize [x,z,z,z,z,z,z,z]
theorem mutable (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_mut_usize (s0 z x0 x1 x2 x3 x4 x5 x6 x7) 0#usize=ok (z,back z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write0 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : back z x0 x1 x2 x3 x4 x5 x6 x7 x0=s1 z x0 x1 x2 x3 x4 x5 x6 x7 := rfl
theorem write1 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s1 z x0 x1 x2 x3 x4 x5 x6 x7) 1#usize x1=ok (s2 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write2 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s2 z x0 x1 x2 x3 x4 x5 x6 x7) 2#usize x2=ok (s3 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write3 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s3 z x0 x1 x2 x3 x4 x5 x6 x7) 3#usize x3=ok (s4 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write4 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s4 z x0 x1 x2 x3 x4 x5 x6 x7) 4#usize x4=ok (s5 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write5 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s5 z x0 x1 x2 x3 x4 x5 x6 x7) 5#usize x5=ok (s6 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write6 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s6 z x0 x1 x2 x3 x4 x5 x6 x7) 6#usize x6=ok (s7 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem write7 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.update (s7 z x0 x1 x2 x3 x4 x5 x6 x7) 7#usize x7=ok (s8 z x0 x1 x2 x3 x4 x5 x6 x7) := by rfl
theorem read0 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s1 z x0 x1 x2 x3 x4 x5 x6 x7) 0#usize=ok x0 := by rfl
theorem read1 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s2 z x0 x1 x2 x3 x4 x5 x6 x7) 1#usize=ok x1 := by rfl
theorem read2 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s3 z x0 x1 x2 x3 x4 x5 x6 x7) 2#usize=ok x2 := by rfl
theorem read3 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s4 z x0 x1 x2 x3 x4 x5 x6 x7) 3#usize=ok x3 := by rfl
theorem read4 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s5 z x0 x1 x2 x3 x4 x5 x6 x7) 4#usize=ok x4 := by rfl
theorem read5 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s6 z x0 x1 x2 x3 x4 x5 x6 x7) 5#usize=ok x5 := by rfl
theorem read6 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s7 z x0 x1 x2 x3 x4 x5 x6 x7) 6#usize=ok x6 := by rfl
theorem read7 (z x0 x1 x2 x3 x4 x5 x6 x7 : α) : Array.index_usize (s8 z x0 x1 x2 x3 x4 x5 x6 x7) 7#usize=ok x7 := by rfl
#print axioms mutable
#print axioms write0
#print axioms write1
#print axioms write2
#print axioms write3
#print axioms write4
#print axioms write5
#print axioms write6
#print axioms write7
#print axioms read0
#print axioms read1
#print axioms read2
#print axioms read3
#print axioms read4
#print axioms read5
#print axioms read6
#print axioms read7
end AspisR1.NBA_Store8
