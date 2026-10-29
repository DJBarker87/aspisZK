import R1Z.PV_RDB2D_PV_B3P_Sorted133
namespace PV_B3P_InputMembers133
open PV_B3P_Sorted133
set_option autoImplicit false
theorem block0 : ([27, 32, 43, 48, 411, 416, 443, 448, 459, 464, 491, 496, 507, 512, 11, 28] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
#print axioms block0
theorem block1 : ([12, 412, 44, 428, 60, 428, 44, 1008, 460, 1010, 508, 1012, 1008, 1014, 1010, 1014] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
#print axioms block1
theorem block2 : ([1012, 1015, 1014, 1015, 64, 1017, 913, 1017, 523, 1018, 475, 540, 523, 540, 1018, 528] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
#print axioms block2
theorem block3 : ([539, 556, 539, 544, 555, 572, 555, 560, 571, 588, 571, 576, 587, 604, 587, 592] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
#print axioms block3
theorem block4 : ([603, 620, 603, 608, 619, 636, 619, 624, 635, 652, 635, 640, 651, 668, 651, 656] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
#print axioms block4
theorem block5 : ([667, 684, 667, 672, 683, 700, 683, 688, 699, 716, 699, 704, 715, 732, 715, 720] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
#print axioms block5
theorem block6 : ([731, 748, 731, 736, 747, 764, 747, 752, 763, 780, 763, 768, 779, 796, 779, 784] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
#print axioms block6
theorem block7 : ([795, 812, 795, 800, 811, 828, 811, 816, 827, 844, 827, 832, 843, 860, 843, 848] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
#print axioms block7
theorem block8 : ([59, 913, 914, 76, 914, 64, 75, 917, 918, 92, 918, 80, 91, 921, 922, 108] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
#print axioms block8
theorem block9 : ([922, 96, 107, 925, 926, 124, 926, 112, 123, 929, 930, 140, 930, 128, 139, 933] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
#print axioms block9
theorem block10 : ([934, 156, 934, 144, 155, 937, 938, 172, 938, 160, 171, 941, 942, 188, 942, 176] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inl (by decide))
#print axioms block10
theorem block11 : ([187, 945, 946, 204, 946, 192, 203, 949, 950, 220, 950, 208, 219, 953, 954, 236] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
#print axioms block11
theorem block12 : ([954, 224, 235, 957, 958, 252, 958, 240, 251, 961, 962, 268, 962, 256, 267, 965] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
#print axioms block12
theorem block13 : ([966, 284, 966, 272, 283, 969, 970, 300, 970, 288, 299, 973, 974, 316, 974, 304] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
#print axioms block13
theorem block14 : ([315, 977, 978, 332, 978, 320, 331, 981, 982, 348, 982, 336, 347, 985, 986, 364] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
#print axioms block14
theorem block15 : ([986, 352, 363, 989, 990, 380, 990, 368, 379, 993, 994, 396, 994, 384, 395, 997] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
#print axioms block15
theorem block16 : ([998, 876, 998, 864, 875, 1001, 1002, 892, 1002, 880, 891, 1005, 1006, 908, 1006, 896] : List Nat) ⊆ expected := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.expected,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
#print axioms block16
theorem subset : input ⊆ expected := by
  intro x hx
  simp only [PV_B3P_Sorted133.input,List.mem_append] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact block0 h
  · exact block1 h
  · exact block2 h
  · exact block3 h
  · exact block4 h
  · exact block5 h
  · exact block6 h
  · exact block7 h
  · exact block8 h
  · exact block9 h
  · exact block10 h
  · exact block11 h
  · exact block12 h
  · exact block13 h
  · exact block14 h
  · exact block15 h
  · exact block16 h
#print axioms subset
end PV_B3P_InputMembers133
