import R1Z.PDict_RowBounds244
set_option autoImplicit false
namespace R1Z.PDict_RowChunk244_3
open Aeneas Aeneas.Std
def part_0 : List U16 := [361#u16, 362#u16, 363#u16, 364#u16, 368#u16, 369#u16, 370#u16, 371#u16, 372#u16, 373#u16, 374#u16, 375#u16, 376#u16, 377#u16, 378#u16, 379#u16]
theorem part_0_length : part_0.length = 16 := rfl
theorem part_0_bound : ∀ x ∈ part_0, x.val < 1024 := by
  intro x member
  simp only [part_0,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_0_length
#print axioms part_0_bound
def part_1 : List U16 := [380#u16, 384#u16, 385#u16, 386#u16, 387#u16, 388#u16, 389#u16, 390#u16, 391#u16, 392#u16, 393#u16, 394#u16, 395#u16, 396#u16, 400#u16, 401#u16]
theorem part_1_length : part_1.length = 16 := rfl
theorem part_1_bound : ∀ x ∈ part_1, x.val < 1024 := by
  intro x member
  simp only [part_1,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_1_length
#print axioms part_1_bound
def part_2 : List U16 := [402#u16, 403#u16, 404#u16, 405#u16, 406#u16, 407#u16, 408#u16, 409#u16, 410#u16, 411#u16, 412#u16, 416#u16, 417#u16, 418#u16, 419#u16, 420#u16]
theorem part_2_length : part_2.length = 16 := rfl
theorem part_2_bound : ∀ x ∈ part_2, x.val < 1024 := by
  intro x member
  simp only [part_2,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_2_length
#print axioms part_2_bound
def part_3 : List U16 := [421#u16, 422#u16, 423#u16, 424#u16, 425#u16, 426#u16, 427#u16, 428#u16, 432#u16, 433#u16, 434#u16, 435#u16, 436#u16, 437#u16, 438#u16, 439#u16]
theorem part_3_length : part_3.length = 16 := rfl
theorem part_3_bound : ∀ x ∈ part_3, x.val < 1024 := by
  intro x member
  simp only [part_3,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_3_length
#print axioms part_3_bound
def part_4 : List U16 := [440#u16, 441#u16, 442#u16, 443#u16, 444#u16, 448#u16, 449#u16, 450#u16, 451#u16, 452#u16, 453#u16, 454#u16, 455#u16, 456#u16, 457#u16, 458#u16]
theorem part_4_length : part_4.length = 16 := rfl
theorem part_4_bound : ∀ x ∈ part_4, x.val < 1024 := by
  intro x member
  simp only [part_4,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_4_length
#print axioms part_4_bound
def part_5 : List U16 := [459#u16, 460#u16, 464#u16, 465#u16, 466#u16, 467#u16, 468#u16, 469#u16, 470#u16, 471#u16, 472#u16, 473#u16, 474#u16, 475#u16, 476#u16, 479#u16]
theorem part_5_length : part_5.length = 16 := rfl
theorem part_5_bound : ∀ x ∈ part_5, x.val < 1024 := by
  intro x member
  simp only [part_5,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_5_length
#print axioms part_5_bound
def part_6 : List U16 := [480#u16, 481#u16, 482#u16, 483#u16, 484#u16, 485#u16, 486#u16, 487#u16, 488#u16, 489#u16, 490#u16, 491#u16, 492#u16, 493#u16, 494#u16, 495#u16]
theorem part_6_length : part_6.length = 16 := rfl
theorem part_6_bound : ∀ x ∈ part_6, x.val < 1024 := by
  intro x member
  simp only [part_6,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals scalar_tac
#print axioms part_6_length
#print axioms part_6_bound
def part_7 : List U16 := [496#u16, 497#u16, 498#u16, 499#u16, 500#u16, 501#u16, 502#u16, 503#u16, 504#u16, 505#u16, 506#u16, 507#u16, 508#u16, 509#u16, 510#u16, 511#u16]
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
end R1Z.PDict_RowChunk244_3
