import R1Z.PV_RDB2D_PV_B3P_Sorted133
namespace PV_B3P_OutputMembers133
open PV_B3P_Sorted133
set_option autoImplicit false
theorem block0 : ([11, 12, 27, 28, 32, 43, 44, 48, 59, 60, 64, 75, 76, 80, 91, 92] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
#print axioms block0
theorem block1 : ([96, 107, 108, 112, 123, 124, 128, 139, 140, 144, 155, 156, 160, 171, 172, 176] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
#print axioms block1
theorem block2 : ([187, 188, 192, 203, 204, 208, 219, 220, 224, 235, 236, 240, 251, 252, 256, 267] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
#print axioms block2
theorem block3 : ([268, 272, 283, 284, 288, 299, 300, 304, 315, 316, 320, 331, 332, 336, 347, 348] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
#print axioms block3
theorem block4 : ([352, 363, 364, 368, 379, 380, 384, 395, 396, 411, 412, 416, 428, 443, 448, 459] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
#print axioms block4
theorem block5 : ([460, 464, 475, 491, 496, 507, 508, 512, 523, 528, 539, 540, 544, 555, 556, 560] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inl (by decide)
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
#print axioms block5
theorem block6 : ([571, 572, 576, 587, 588, 592, 603, 604, 608, 619, 620, 624, 635, 636, 640, 651] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
#print axioms block6
theorem block7 : ([652, 656, 667, 668, 672, 683, 684, 688, 699, 700, 704, 715, 716, 720, 731, 732] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
#print axioms block7
theorem block8 : ([736, 747, 748, 752, 763, 764, 768, 779, 780, 784, 795, 796, 800, 811, 812, 816] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
#print axioms block8
theorem block9 : ([827, 828, 832, 843, 844, 848, 860, 864, 875, 876, 880, 891, 892, 896, 908, 913] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
#print axioms block9
theorem block10 : ([914, 917, 918, 921, 922, 925, 926, 929, 930, 933, 934, 937, 938, 941, 942, 945] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
#print axioms block10
theorem block11 : ([946, 949, 950, 953, 954, 957, 958, 961, 962, 965, 966, 969, 970, 973, 974, 977] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
#print axioms block11
theorem block12 : ([978, 981, 982, 985, 986, 989, 990, 993, 994, 997, 998, 1001, 1002, 1005, 1006, 1008] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))))))))))))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
#print axioms block12
theorem block13 : ([1010, 1012, 1014, 1015, 1017, 1018] : List Nat) ⊆ input := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inl (by decide))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp only [PV_B3P_Sorted133.input,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (by decide)))
#print axioms block13
theorem subset : expected ⊆ input := by
  intro x hx
  simp only [PV_B3P_Sorted133.expected,List.mem_append] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
#print axioms subset
end PV_B3P_OutputMembers133
