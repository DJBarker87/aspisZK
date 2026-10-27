import R1Z.PDict_RowBounds244
set_option autoImplicit false
namespace R1Z.PDict_RowChunk244_2
open Aeneas Aeneas.Std
def part_0 : List U16 := [203#u16, 204#u16, 208#u16, 209#u16, 210#u16, 211#u16, 212#u16, 213#u16, 214#u16, 215#u16, 216#u16, 217#u16, 218#u16, 219#u16, 220#u16, 224#u16]
theorem part_0_length : part_0.length = 16 := rfl
theorem part_0_bound : ∀ x ∈ part_0, x.val < 1024 := by
  intro x member
  simp only [part_0,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_0_length
#print axioms part_0_bound
def part_1 : List U16 := [225#u16, 226#u16, 227#u16, 228#u16, 229#u16, 230#u16, 231#u16, 232#u16, 233#u16, 234#u16, 235#u16, 236#u16, 240#u16, 241#u16, 242#u16, 243#u16]
theorem part_1_length : part_1.length = 16 := rfl
theorem part_1_bound : ∀ x ∈ part_1, x.val < 1024 := by
  intro x member
  simp only [part_1,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_1_length
#print axioms part_1_bound
def part_2 : List U16 := [244#u16, 245#u16, 246#u16, 247#u16, 248#u16, 249#u16, 250#u16, 251#u16, 252#u16, 256#u16, 257#u16, 258#u16, 259#u16, 260#u16, 261#u16, 262#u16]
theorem part_2_length : part_2.length = 16 := rfl
theorem part_2_bound : ∀ x ∈ part_2, x.val < 1024 := by
  intro x member
  simp only [part_2,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_2_length
#print axioms part_2_bound
def part_3 : List U16 := [263#u16, 264#u16, 265#u16, 266#u16, 267#u16, 268#u16, 272#u16, 273#u16, 274#u16, 275#u16, 276#u16, 277#u16, 278#u16, 279#u16, 280#u16, 281#u16]
theorem part_3_length : part_3.length = 16 := rfl
theorem part_3_bound : ∀ x ∈ part_3, x.val < 1024 := by
  intro x member
  simp only [part_3,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_3_length
#print axioms part_3_bound
def part_4 : List U16 := [282#u16, 283#u16, 284#u16, 288#u16, 289#u16, 290#u16, 291#u16, 292#u16, 293#u16, 294#u16, 295#u16, 296#u16, 297#u16, 298#u16, 299#u16, 300#u16]
theorem part_4_length : part_4.length = 16 := rfl
theorem part_4_bound : ∀ x ∈ part_4, x.val < 1024 := by
  intro x member
  simp only [part_4,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_4_length
#print axioms part_4_bound
def part_5 : List U16 := [304#u16, 305#u16, 306#u16, 307#u16, 308#u16, 309#u16, 310#u16, 311#u16, 312#u16, 313#u16, 314#u16, 315#u16, 316#u16, 320#u16, 321#u16, 322#u16]
theorem part_5_length : part_5.length = 16 := rfl
theorem part_5_bound : ∀ x ∈ part_5, x.val < 1024 := by
  intro x member
  simp only [part_5,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_5_length
#print axioms part_5_bound
def part_6 : List U16 := [323#u16, 324#u16, 325#u16, 326#u16, 327#u16, 328#u16, 329#u16, 330#u16, 331#u16, 332#u16, 336#u16, 337#u16, 338#u16, 339#u16, 340#u16, 341#u16]
theorem part_6_length : part_6.length = 16 := rfl
theorem part_6_bound : ∀ x ∈ part_6, x.val < 1024 := by
  intro x member
  simp only [part_6,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_6_length
#print axioms part_6_bound
def part_7 : List U16 := [342#u16, 343#u16, 344#u16, 345#u16, 346#u16, 347#u16, 348#u16, 352#u16, 353#u16, 354#u16, 355#u16, 356#u16, 357#u16, 358#u16, 359#u16, 360#u16]
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
end R1Z.PDict_RowChunk244_2
