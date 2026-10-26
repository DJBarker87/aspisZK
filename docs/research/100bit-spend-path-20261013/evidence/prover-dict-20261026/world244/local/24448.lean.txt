import R1Z.PDict_RowBounds244
set_option autoImplicit false
namespace R1Z.PDict_RowChunk244_1
open Aeneas Aeneas.Std
def part_0 : List U16 := [48#u16, 49#u16, 50#u16, 51#u16, 52#u16, 53#u16, 54#u16, 55#u16, 56#u16, 57#u16, 58#u16, 59#u16, 60#u16, 64#u16, 65#u16, 66#u16]
theorem part_0_length : part_0.length = 16 := rfl
theorem part_0_bound : ∀ x ∈ part_0, x.val < 1024 := by
  intro x member
  simp only [part_0,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_0_length
#print axioms part_0_bound
def part_1 : List U16 := [67#u16, 68#u16, 69#u16, 70#u16, 71#u16, 72#u16, 73#u16, 74#u16, 75#u16, 76#u16, 80#u16, 81#u16, 82#u16, 83#u16, 84#u16, 85#u16]
theorem part_1_length : part_1.length = 16 := rfl
theorem part_1_bound : ∀ x ∈ part_1, x.val < 1024 := by
  intro x member
  simp only [part_1,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_1_length
#print axioms part_1_bound
def part_2 : List U16 := [86#u16, 87#u16, 88#u16, 89#u16, 90#u16, 91#u16, 92#u16, 96#u16, 97#u16, 98#u16, 99#u16, 100#u16, 101#u16, 102#u16, 103#u16, 104#u16]
theorem part_2_length : part_2.length = 16 := rfl
theorem part_2_bound : ∀ x ∈ part_2, x.val < 1024 := by
  intro x member
  simp only [part_2,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_2_length
#print axioms part_2_bound
def part_3 : List U16 := [105#u16, 106#u16, 107#u16, 108#u16, 112#u16, 113#u16, 114#u16, 115#u16, 116#u16, 117#u16, 118#u16, 119#u16, 120#u16, 121#u16, 122#u16, 123#u16]
theorem part_3_length : part_3.length = 16 := rfl
theorem part_3_bound : ∀ x ∈ part_3, x.val < 1024 := by
  intro x member
  simp only [part_3,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_3_length
#print axioms part_3_bound
def part_4 : List U16 := [124#u16, 128#u16, 129#u16, 130#u16, 131#u16, 132#u16, 133#u16, 134#u16, 135#u16, 136#u16, 137#u16, 138#u16, 139#u16, 140#u16, 144#u16, 145#u16]
theorem part_4_length : part_4.length = 16 := rfl
theorem part_4_bound : ∀ x ∈ part_4, x.val < 1024 := by
  intro x member
  simp only [part_4,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_4_length
#print axioms part_4_bound
def part_5 : List U16 := [146#u16, 147#u16, 148#u16, 149#u16, 150#u16, 151#u16, 152#u16, 153#u16, 154#u16, 155#u16, 156#u16, 160#u16, 161#u16, 162#u16, 163#u16, 164#u16]
theorem part_5_length : part_5.length = 16 := rfl
theorem part_5_bound : ∀ x ∈ part_5, x.val < 1024 := by
  intro x member
  simp only [part_5,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_5_length
#print axioms part_5_bound
def part_6 : List U16 := [165#u16, 166#u16, 167#u16, 168#u16, 169#u16, 170#u16, 171#u16, 172#u16, 176#u16, 177#u16, 178#u16, 179#u16, 180#u16, 181#u16, 182#u16, 183#u16]
theorem part_6_length : part_6.length = 16 := rfl
theorem part_6_bound : ∀ x ∈ part_6, x.val < 1024 := by
  intro x member
  simp only [part_6,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_6_length
#print axioms part_6_bound
def part_7 : List U16 := [184#u16, 185#u16, 186#u16, 187#u16, 188#u16, 192#u16, 193#u16, 194#u16, 195#u16, 196#u16, 197#u16, 198#u16, 199#u16, 200#u16, 201#u16, 202#u16]
theorem part_7_length : part_7.length = 16 := rfl
theorem part_7_bound : ∀ x ∈ part_7, x.val < 1024 := by
  intro x member
  simp only [part_7,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_7_length
#print axioms part_7_bound
def values : List U16 := part_0 ++ part_1 ++ part_2 ++ part_3 ++ part_4 ++ part_5 ++ part_6 ++ part_7
theorem length : values.length = 128 := by
  simp only [values,List.length_append,part_0_length, part_1_length, part_2_length, part_3_length, part_4_length, part_5_length, part_6_length, part_7_length]
theorem bound : ∀ x ∈ values, x.val < 1024 :=
  (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ (PDict_RowBounds244.append_bound _ _ part_0_bound part_1_bound) part_2_bound) part_3_bound) part_4_bound) part_5_bound) part_6_bound) part_7_bound)
#print axioms length
#print axioms bound
end R1Z.PDict_RowChunk244_1
