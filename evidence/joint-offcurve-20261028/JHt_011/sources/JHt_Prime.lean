import JHt_PrattCore
set_option autoImplicit false
namespace AspisR1.JHt_Prime
open JHt_BinaryModPow JHt_PrattCore
attribute [local irreducible] modPow
theorem prime_2 : Nat.Prime 2 := by norm_num
#print axioms prime_2
theorem prime_3 : Nat.Prime 3 := by norm_num
#print axioms prime_3
theorem prime_17 : Nat.Prime 17 := by norm_num
#print axioms prime_17
theorem prime_7 : Nat.Prime 7 := by norm_num
#print axioms prime_7
theorem prime_239 : Nat.Prime 239 := by norm_num
#print axioms prime_239
theorem prime_479 : Nat.Prime 479 := by norm_num
#print axioms prime_479
theorem exp_32573_0 : modPow 2 32572 32573 256 = 1 := by decide +kernel
#print axioms exp_32573_0
theorem exp_32573_1 : modPow 2 16286 32573 256 = 32572 := by decide +kernel
#print axioms exp_32573_1
theorem exp_32573_2 : modPow 2 1916 32573 256 = 19735 := by decide +kernel
#print axioms exp_32573_2
theorem exp_32573_3 : modPow 2 68 32573 256 = 10721 := by decide +kernel
#print axioms exp_32573_3
theorem prime_32573 : Nat.Prime 32573 := by
  apply certificate 32573 2 256 (by decide) [2, 2, 17, 479]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_17 | exact prime_479
  · decide
  · exact exp_32573_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((32573-1)/2) 32573 256) 1 32573).mp heq
      rw [exp_32573_1] at hh
      exact (by decide : 32572 % 32573 ≠ 1 % 32573) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((32573-1)/2) 32573 256) 1 32573).mp heq
      rw [exp_32573_1] at hh
      exact (by decide : 32572 % 32573 ≠ 1 % 32573) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((32573-1)/17) 32573 256) 1 32573).mp heq
      rw [exp_32573_2] at hh
      exact (by decide : 19735 % 32573 ≠ 1 % 32573) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((32573-1)/479) 32573 256) 1 32573).mp heq
      rw [exp_32573_3] at hh
      exact (by decide : 10721 % 32573 ≠ 1 % 32573) hh
#print axioms prime_32573
theorem exp_65147_0 : modPow 2 65146 65147 256 = 1 := by decide +kernel
#print axioms exp_65147_0
theorem exp_65147_1 : modPow 2 32573 65147 256 = 65146 := by decide +kernel
#print axioms exp_65147_1
theorem exp_65147_2 : modPow 2 2 65147 256 = 4 := by decide +kernel
#print axioms exp_65147_2
theorem prime_65147 : Nat.Prime 65147 := by
  apply certificate 65147 2 256 (by decide) [2, 32573]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals first | exact prime_2 | exact prime_32573
  · decide
  · exact exp_65147_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((65147-1)/2) 65147 256) 1 65147).mp heq
      rw [exp_65147_1] at hh
      exact (by decide : 65146 % 65147 ≠ 1 % 65147) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((65147-1)/32573) 65147 256) 1 65147).mp heq
      rw [exp_65147_2] at hh
      exact (by decide : 4 % 65147 ≠ 1 % 65147) hh
#print axioms prime_65147
theorem prime_5 : Nat.Prime 5 := by norm_num
#print axioms prime_5
theorem prime_11 : Nat.Prime 11 := by norm_num
#print axioms prime_11
theorem prime_353 : Nat.Prime 353 := by norm_num
#print axioms prime_353
theorem prime_29 : Nat.Prime 29 := by norm_num
#print axioms prime_29
theorem prime_59 : Nat.Prime 59 := by norm_num
#print axioms prime_59
theorem prime_487 : Nat.Prime 487 := by norm_num
#print axioms prime_487
theorem exp_57467_0 : modPow 2 57466 57467 256 = 1 := by decide +kernel
#print axioms exp_57467_0
theorem exp_57467_1 : modPow 2 28733 57467 256 = 57466 := by decide +kernel
#print axioms exp_57467_1
theorem exp_57467_2 : modPow 2 974 57467 256 = 40207 := by decide +kernel
#print axioms exp_57467_2
theorem exp_57467_3 : modPow 2 118 57467 256 = 17139 := by decide +kernel
#print axioms exp_57467_3
theorem prime_57467 : Nat.Prime 57467 := by
  apply certificate 57467 2 256 (by decide) [2, 59, 487]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_59 | exact prime_487
  · decide
  · exact exp_57467_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57467-1)/2) 57467 256) 1 57467).mp heq
      rw [exp_57467_1] at hh
      exact (by decide : 57466 % 57467 ≠ 1 % 57467) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57467-1)/59) 57467 256) 1 57467).mp heq
      rw [exp_57467_2] at hh
      exact (by decide : 40207 % 57467 ≠ 1 % 57467) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57467-1)/487) 57467 256) 1 57467).mp heq
      rw [exp_57467_3] at hh
      exact (by decide : 17139 % 57467 ≠ 1 % 57467) hh
#print axioms prime_57467
theorem prime_13 : Nat.Prime 13 := by norm_num
#print axioms prime_13
theorem prime_131 : Nat.Prime 131 := by norm_num
#print axioms prime_131
theorem exp_132049_0 : modPow 26 132048 132049 256 = 1 := by decide +kernel
#print axioms exp_132049_0
theorem exp_132049_1 : modPow 26 66024 132049 256 = 132048 := by decide +kernel
#print axioms exp_132049_1
theorem exp_132049_2 : modPow 26 44016 132049 256 = 2743 := by decide +kernel
#print axioms exp_132049_2
theorem exp_132049_3 : modPow 26 18864 132049 256 = 31672 := by decide +kernel
#print axioms exp_132049_3
theorem exp_132049_4 : modPow 26 1008 132049 256 = 94691 := by decide +kernel
#print axioms exp_132049_4
theorem prime_132049 : Nat.Prime 132049 := by
  apply certificate 132049 26 256 (by decide) [2, 2, 2, 2, 3, 3, 7, 131]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_7 | exact prime_131
  · decide
  · exact exp_132049_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/2) 132049 256) 1 132049).mp heq
      rw [exp_132049_1] at hh
      exact (by decide : 132048 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/2) 132049 256) 1 132049).mp heq
      rw [exp_132049_1] at hh
      exact (by decide : 132048 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/2) 132049 256) 1 132049).mp heq
      rw [exp_132049_1] at hh
      exact (by decide : 132048 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/2) 132049 256) 1 132049).mp heq
      rw [exp_132049_1] at hh
      exact (by decide : 132048 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/3) 132049 256) 1 132049).mp heq
      rw [exp_132049_2] at hh
      exact (by decide : 2743 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/3) 132049 256) 1 132049).mp heq
      rw [exp_132049_2] at hh
      exact (by decide : 2743 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/7) 132049 256) 1 132049).mp heq
      rw [exp_132049_3] at hh
      exact (by decide : 31672 % 132049 ≠ 1 % 132049) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 26 ((132049-1)/131) 132049 256) 1 132049).mp heq
      rw [exp_132049_4] at hh
      exact (by decide : 94691 % 132049 ≠ 1 % 132049) hh
#print axioms prime_132049
theorem prime_43 : Nat.Prime 43 := by norm_num
#print axioms prime_43
theorem prime_23 : Nat.Prime 23 := by norm_num
#print axioms prime_23
theorem exp_3727_0 : modPow 3 3726 3727 256 = 1 := by decide +kernel
#print axioms exp_3727_0
theorem exp_3727_1 : modPow 3 1863 3727 256 = 3726 := by decide +kernel
#print axioms exp_3727_1
theorem exp_3727_2 : modPow 3 1242 3727 256 = 2538 := by decide +kernel
#print axioms exp_3727_2
theorem exp_3727_3 : modPow 3 162 3727 256 = 2644 := by decide +kernel
#print axioms exp_3727_3
theorem prime_3727 : Nat.Prime 3727 := by
  apply certificate 3727 3 256 (by decide) [2, 3, 3, 3, 3, 23]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_23
  · decide
  · exact exp_3727_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((3727-1)/2) 3727 256) 1 3727).mp heq
      rw [exp_3727_1] at hh
      exact (by decide : 3726 % 3727 ≠ 1 % 3727) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((3727-1)/3) 3727 256) 1 3727).mp heq
      rw [exp_3727_2] at hh
      exact (by decide : 2538 % 3727 ≠ 1 % 3727) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((3727-1)/3) 3727 256) 1 3727).mp heq
      rw [exp_3727_2] at hh
      exact (by decide : 2538 % 3727 ≠ 1 % 3727) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((3727-1)/3) 3727 256) 1 3727).mp heq
      rw [exp_3727_2] at hh
      exact (by decide : 2538 % 3727 ≠ 1 % 3727) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((3727-1)/3) 3727 256) 1 3727).mp heq
      rw [exp_3727_2] at hh
      exact (by decide : 2538 % 3727 ≠ 1 % 3727) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((3727-1)/23) 3727 256) 1 3727).mp heq
      rw [exp_3727_3] at hh
      exact (by decide : 2644 % 3727 ≠ 1 % 3727) hh
#print axioms prime_3727
theorem exp_1923133_0 : modPow 2 1923132 1923133 256 = 1 := by decide +kernel
#print axioms exp_1923133_0
theorem exp_1923133_1 : modPow 2 961566 1923133 256 = 1923132 := by decide +kernel
#print axioms exp_1923133_1
theorem exp_1923133_2 : modPow 2 641044 1923133 256 = 1862225 := by decide +kernel
#print axioms exp_1923133_2
theorem exp_1923133_3 : modPow 2 44724 1923133 256 = 1760861 := by decide +kernel
#print axioms exp_1923133_3
theorem exp_1923133_4 : modPow 2 516 1923133 256 = 740012 := by decide +kernel
#print axioms exp_1923133_4
theorem prime_1923133 : Nat.Prime 1923133 := by
  apply certificate 1923133 2 256 (by decide) [2, 2, 3, 43, 3727]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_43 | exact prime_3727
  · decide
  · exact exp_1923133_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1923133-1)/2) 1923133 256) 1 1923133).mp heq
      rw [exp_1923133_1] at hh
      exact (by decide : 1923132 % 1923133 ≠ 1 % 1923133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1923133-1)/2) 1923133 256) 1 1923133).mp heq
      rw [exp_1923133_1] at hh
      exact (by decide : 1923132 % 1923133 ≠ 1 % 1923133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1923133-1)/3) 1923133 256) 1 1923133).mp heq
      rw [exp_1923133_2] at hh
      exact (by decide : 1862225 % 1923133 ≠ 1 % 1923133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1923133-1)/43) 1923133 256) 1 1923133).mp heq
      rw [exp_1923133_3] at hh
      exact (by decide : 1760861 % 1923133 ≠ 1 % 1923133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1923133-1)/3727) 1923133 256) 1 1923133).mp heq
      rw [exp_1923133_4] at hh
      exact (by decide : 740012 % 1923133 ≠ 1 % 1923133) hh
#print axioms prime_1923133
theorem prime_31 : Nat.Prime 31 := by norm_num
#print axioms prime_31
theorem prime_53 : Nat.Prime 53 := by norm_num
#print axioms prime_53
theorem prime_107 : Nat.Prime 107 := by norm_num
#print axioms prime_107
theorem prime_37 : Nat.Prime 37 := by norm_num
#print axioms prime_37
theorem prime_223 : Nat.Prime 223 := by norm_num
#print axioms prime_223
theorem prime_173 : Nat.Prime 173 := by norm_num
#print axioms prime_173
theorem exp_4153_0 : modPow 5 4152 4153 256 = 1 := by decide +kernel
#print axioms exp_4153_0
theorem exp_4153_1 : modPow 5 2076 4153 256 = 4152 := by decide +kernel
#print axioms exp_4153_1
theorem exp_4153_2 : modPow 5 1384 4153 256 = 3982 := by decide +kernel
#print axioms exp_4153_2
theorem exp_4153_3 : modPow 5 24 4153 256 = 292 := by decide +kernel
#print axioms exp_4153_3
theorem prime_4153 : Nat.Prime 4153 := by
  apply certificate 4153 5 256 (by decide) [2, 2, 2, 3, 173]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_173
  · decide
  · exact exp_4153_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((4153-1)/2) 4153 256) 1 4153).mp heq
      rw [exp_4153_1] at hh
      exact (by decide : 4152 % 4153 ≠ 1 % 4153) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((4153-1)/2) 4153 256) 1 4153).mp heq
      rw [exp_4153_1] at hh
      exact (by decide : 4152 % 4153 ≠ 1 % 4153) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((4153-1)/2) 4153 256) 1 4153).mp heq
      rw [exp_4153_1] at hh
      exact (by decide : 4152 % 4153 ≠ 1 % 4153) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((4153-1)/3) 4153 256) 1 4153).mp heq
      rw [exp_4153_2] at hh
      exact (by decide : 3982 % 4153 ≠ 1 % 4153) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((4153-1)/173) 4153 256) 1 4153).mp heq
      rw [exp_4153_3] at hh
      exact (by decide : 292 % 4153 ≠ 1 % 4153) hh
#print axioms prime_4153
theorem prime_41 : Nat.Prime 41 := by norm_num
#print axioms prime_41
theorem exp_1723_0 : modPow 3 1722 1723 256 = 1 := by decide +kernel
#print axioms exp_1723_0
theorem exp_1723_1 : modPow 3 861 1723 256 = 1722 := by decide +kernel
#print axioms exp_1723_1
theorem exp_1723_2 : modPow 3 574 1723 256 = 1681 := by decide +kernel
#print axioms exp_1723_2
theorem exp_1723_3 : modPow 3 246 1723 256 = 555 := by decide +kernel
#print axioms exp_1723_3
theorem exp_1723_4 : modPow 3 42 1723 256 = 1462 := by decide +kernel
#print axioms exp_1723_4
theorem prime_1723 : Nat.Prime 1723 := by
  apply certificate 1723 3 256 (by decide) [2, 3, 7, 41]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_7 | exact prime_41
  · decide
  · exact exp_1723_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((1723-1)/2) 1723 256) 1 1723).mp heq
      rw [exp_1723_1] at hh
      exact (by decide : 1722 % 1723 ≠ 1 % 1723) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((1723-1)/3) 1723 256) 1 1723).mp heq
      rw [exp_1723_2] at hh
      exact (by decide : 1681 % 1723 ≠ 1 % 1723) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((1723-1)/7) 1723 256) 1 1723).mp heq
      rw [exp_1723_3] at hh
      exact (by decide : 555 % 1723 ≠ 1 % 1723) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((1723-1)/41) 1723 256) 1 1723).mp heq
      rw [exp_1723_4] at hh
      exact (by decide : 1462 % 1723 ≠ 1 % 1723) hh
#print axioms prime_1723
theorem exp_430751_0 : modPow 17 430750 430751 256 = 1 := by decide +kernel
#print axioms exp_430751_0
theorem exp_430751_1 : modPow 17 215375 430751 256 = 430750 := by decide +kernel
#print axioms exp_430751_1
theorem exp_430751_2 : modPow 17 86150 430751 256 = 202197 := by decide +kernel
#print axioms exp_430751_2
theorem exp_430751_3 : modPow 17 250 430751 256 = 109979 := by decide +kernel
#print axioms exp_430751_3
theorem prime_430751 : Nat.Prime 430751 := by
  apply certificate 430751 17 256 (by decide) [2, 5, 5, 5, 1723]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_5 | exact prime_1723
  · decide
  · exact exp_430751_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 17 ((430751-1)/2) 430751 256) 1 430751).mp heq
      rw [exp_430751_1] at hh
      exact (by decide : 430750 % 430751 ≠ 1 % 430751) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 17 ((430751-1)/5) 430751 256) 1 430751).mp heq
      rw [exp_430751_2] at hh
      exact (by decide : 202197 % 430751 ≠ 1 % 430751) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 17 ((430751-1)/5) 430751 256) 1 430751).mp heq
      rw [exp_430751_2] at hh
      exact (by decide : 202197 % 430751 ≠ 1 % 430751) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 17 ((430751-1)/5) 430751 256) 1 430751).mp heq
      rw [exp_430751_2] at hh
      exact (by decide : 202197 % 430751 ≠ 1 % 430751) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 17 ((430751-1)/1723) 430751 256) 1 430751).mp heq
      rw [exp_430751_3] at hh
      exact (by decide : 109979 % 430751 ≠ 1 % 430751) hh
#print axioms prime_430751
theorem exp_31757755568855353_0 : modPow 10 31757755568855352 31757755568855353 256 = 1 := by decide +kernel
#print axioms exp_31757755568855353_0
theorem exp_31757755568855353_1 : modPow 10 15878877784427676 31757755568855353 256 = 31757755568855352 := by decide +kernel
#print axioms exp_31757755568855353_1
theorem exp_31757755568855353_2 : modPow 10 10585918522951784 31757755568855353 256 = 22133410514677784 := by decide +kernel
#print axioms exp_31757755568855353_2
theorem exp_31757755568855353_3 : modPow 10 1024443728027592 31757755568855353 256 = 24776906756080210 := by decide +kernel
#print axioms exp_31757755568855353_3
theorem exp_31757755568855353_4 : modPow 10 296801453914536 31757755568855353 256 = 30702321360579269 := by decide +kernel
#print axioms exp_31757755568855353_4
theorem exp_31757755568855353_5 : modPow 10 142411459950024 31757755568855353 256 = 5141820974828509 := by decide +kernel
#print axioms exp_31757755568855353_5
theorem exp_31757755568855353_6 : modPow 10 7646943310584 31757755568855353 256 = 29494927157741833 := by decide +kernel
#print axioms exp_31757755568855353_6
theorem exp_31757755568855353_7 : modPow 10 73726481352 31757755568855353 256 = 25185179080663893 := by decide +kernel
#print axioms exp_31757755568855353_7
theorem prime_31757755568855353 : Nat.Prime 31757755568855353 := by
  apply certificate 31757755568855353 10 256 (by decide) [2, 2, 2, 3, 31, 107, 223, 4153, 430751]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_31 | exact prime_107 | exact prime_223 | exact prime_4153 | exact prime_430751
  · decide
  · exact exp_31757755568855353_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/2) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_1] at hh
      exact (by decide : 31757755568855352 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/2) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_1] at hh
      exact (by decide : 31757755568855352 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/2) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_1] at hh
      exact (by decide : 31757755568855352 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/3) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_2] at hh
      exact (by decide : 22133410514677784 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/31) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_3] at hh
      exact (by decide : 24776906756080210 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/107) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_4] at hh
      exact (by decide : 30702321360579269 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/223) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_5] at hh
      exact (by decide : 5141820974828509 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/4153) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_6] at hh
      exact (by decide : 29494927157741833 % 31757755568855353 ≠ 1 % 31757755568855353) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 10 ((31757755568855353-1)/430751) 31757755568855353 256) 1 31757755568855353).mp heq
      rw [exp_31757755568855353_7] at hh
      exact (by decide : 25185179080663893 % 31757755568855353 ≠ 1 % 31757755568855353) hh
#print axioms prime_31757755568855353
theorem prime_19 : Nat.Prime 19 := by norm_num
#print axioms prime_19
theorem prime_83 : Nat.Prime 83 := by norm_num
#print axioms prime_83
theorem exp_9463_0 : modPow 3 9462 9463 256 = 1 := by decide +kernel
#print axioms exp_9463_0
theorem exp_9463_1 : modPow 3 4731 9463 256 = 9462 := by decide +kernel
#print axioms exp_9463_1
theorem exp_9463_2 : modPow 3 3154 9463 256 = 607 := by decide +kernel
#print axioms exp_9463_2
theorem exp_9463_3 : modPow 3 498 9463 256 = 682 := by decide +kernel
#print axioms exp_9463_3
theorem exp_9463_4 : modPow 3 114 9463 256 = 8732 := by decide +kernel
#print axioms exp_9463_4
theorem prime_9463 : Nat.Prime 9463 := by
  apply certificate 9463 3 256 (by decide) [2, 3, 19, 83]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_19 | exact prime_83
  · decide
  · exact exp_9463_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((9463-1)/2) 9463 256) 1 9463).mp heq
      rw [exp_9463_1] at hh
      exact (by decide : 9462 % 9463 ≠ 1 % 9463) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((9463-1)/3) 9463 256) 1 9463).mp heq
      rw [exp_9463_2] at hh
      exact (by decide : 607 % 9463 ≠ 1 % 9463) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((9463-1)/19) 9463 256) 1 9463).mp heq
      rw [exp_9463_3] at hh
      exact (by decide : 682 % 9463 ≠ 1 % 9463) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 3 ((9463-1)/83) 9463 256) 1 9463).mp heq
      rw [exp_9463_4] at hh
      exact (by decide : 8732 % 9463 ≠ 1 % 9463) hh
#print axioms prime_9463
theorem exp_37853_0 : modPow 2 37852 37853 256 = 1 := by decide +kernel
#print axioms exp_37853_0
theorem exp_37853_1 : modPow 2 18926 37853 256 = 37852 := by decide +kernel
#print axioms exp_37853_1
theorem exp_37853_2 : modPow 2 4 37853 256 = 16 := by decide +kernel
#print axioms exp_37853_2
theorem prime_37853 : Nat.Prime 37853 := by
  apply certificate 37853 2 256 (by decide) [2, 2, 9463]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_9463
  · decide
  · exact exp_37853_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((37853-1)/2) 37853 256) 1 37853).mp heq
      rw [exp_37853_1] at hh
      exact (by decide : 37852 % 37853 ≠ 1 % 37853) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((37853-1)/2) 37853 256) 1 37853).mp heq
      rw [exp_37853_1] at hh
      exact (by decide : 37852 % 37853 ≠ 1 % 37853) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((37853-1)/9463) 37853 256) 1 37853).mp heq
      rw [exp_37853_2] at hh
      exact (by decide : 16 % 37853 ≠ 1 % 37853) hh
#print axioms prime_37853
theorem exp_75707_0 : modPow 2 75706 75707 256 = 1 := by decide +kernel
#print axioms exp_75707_0
theorem exp_75707_1 : modPow 2 37853 75707 256 = 75706 := by decide +kernel
#print axioms exp_75707_1
theorem exp_75707_2 : modPow 2 2 75707 256 = 4 := by decide +kernel
#print axioms exp_75707_2
theorem prime_75707 : Nat.Prime 75707 := by
  apply certificate 75707 2 256 (by decide) [2, 37853]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals first | exact prime_2 | exact prime_37853
  · decide
  · exact exp_75707_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((75707-1)/2) 75707 256) 1 75707).mp heq
      rw [exp_75707_1] at hh
      exact (by decide : 75706 % 75707 ≠ 1 % 75707) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((75707-1)/37853) 75707 256) 1 75707).mp heq
      rw [exp_75707_2] at hh
      exact (by decide : 4 % 75707 ≠ 1 % 75707) hh
#print axioms prime_75707
theorem prime_47 : Nat.Prime 47 := by norm_num
#print axioms prime_47
theorem prime_127 : Nat.Prime 127 := by norm_num
#print axioms prime_127
theorem prime_103 : Nat.Prime 103 := by norm_num
#print axioms prime_103
theorem prime_991 : Nat.Prime 991 := by norm_num
#print axioms prime_991
theorem exp_8574133_0 : modPow 2 8574132 8574133 256 = 1 := by decide +kernel
#print axioms exp_8574133_0
theorem exp_8574133_1 : modPow 2 4287066 8574133 256 = 8574132 := by decide +kernel
#print axioms exp_8574133_1
theorem exp_8574133_2 : modPow 2 2858044 8574133 256 = 7079057 := by decide +kernel
#print axioms exp_8574133_2
theorem exp_8574133_3 : modPow 2 1224876 8574133 256 = 7470406 := by decide +kernel
#print axioms exp_8574133_3
theorem exp_8574133_4 : modPow 2 83244 8574133 256 = 4321357 := by decide +kernel
#print axioms exp_8574133_4
theorem exp_8574133_5 : modPow 2 8652 8574133 256 = 3435729 := by decide +kernel
#print axioms exp_8574133_5
theorem prime_8574133 : Nat.Prime 8574133 := by
  apply certificate 8574133 2 256 (by decide) [2, 2, 3, 7, 103, 991]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_7 | exact prime_103 | exact prime_991
  · decide
  · exact exp_8574133_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((8574133-1)/2) 8574133 256) 1 8574133).mp heq
      rw [exp_8574133_1] at hh
      exact (by decide : 8574132 % 8574133 ≠ 1 % 8574133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((8574133-1)/2) 8574133 256) 1 8574133).mp heq
      rw [exp_8574133_1] at hh
      exact (by decide : 8574132 % 8574133 ≠ 1 % 8574133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((8574133-1)/3) 8574133 256) 1 8574133).mp heq
      rw [exp_8574133_2] at hh
      exact (by decide : 7079057 % 8574133 ≠ 1 % 8574133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((8574133-1)/7) 8574133 256) 1 8574133).mp heq
      rw [exp_8574133_3] at hh
      exact (by decide : 7470406 % 8574133 ≠ 1 % 8574133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((8574133-1)/103) 8574133 256) 1 8574133).mp heq
      rw [exp_8574133_4] at hh
      exact (by decide : 4321357 % 8574133 ≠ 1 % 8574133) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((8574133-1)/991) 8574133 256) 1 8574133).mp heq
      rw [exp_8574133_5] at hh
      exact (by decide : 3435729 % 8574133 ≠ 1 % 8574133) hh
#print axioms prime_8574133
theorem exp_1919519569386763_0 : modPow 2 1919519569386762 1919519569386763 256 = 1 := by decide +kernel
#print axioms exp_1919519569386763_0
theorem exp_1919519569386763_1 : modPow 2 959759784693381 1919519569386763 256 = 1919519569386762 := by decide +kernel
#print axioms exp_1919519569386763_1
theorem exp_1919519569386763_2 : modPow 2 639839856462254 1919519569386763 256 = 1786118255295340 := by decide +kernel
#print axioms exp_1919519569386763_2
theorem exp_1919519569386763_3 : modPow 2 274217081340966 1919519569386763 256 = 1124719358789780 := by decide +kernel
#print axioms exp_1919519569386763_3
theorem exp_1919519569386763_4 : modPow 2 101027345757198 1919519569386763 256 = 602275051902557 := by decide +kernel
#print axioms exp_1919519569386763_4
theorem exp_1919519569386763_5 : modPow 2 40840841901846 1919519569386763 256 = 621931926534591 := by decide +kernel
#print axioms exp_1919519569386763_5
theorem exp_1919519569386763_6 : modPow 2 15114327318006 1919519569386763 256 = 576774792492622 := by decide +kernel
#print axioms exp_1919519569386763_6
theorem exp_1919519569386763_7 : modPow 2 223873314 1919519569386763 256 = 1059928654987441 := by decide +kernel
#print axioms exp_1919519569386763_7
theorem prime_1919519569386763 : Nat.Prime 1919519569386763 := by
  apply certificate 1919519569386763 2 256 (by decide) [2, 3, 7, 19, 47, 47, 127, 8574133]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_7 | exact prime_19 | exact prime_47 | exact prime_127 | exact prime_8574133
  · decide
  · exact exp_1919519569386763_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/2) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_1] at hh
      exact (by decide : 1919519569386762 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/3) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_2] at hh
      exact (by decide : 1786118255295340 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/7) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_3] at hh
      exact (by decide : 1124719358789780 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/19) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_4] at hh
      exact (by decide : 602275051902557 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/47) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_5] at hh
      exact (by decide : 621931926534591 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/47) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_5] at hh
      exact (by decide : 621931926534591 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/127) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_6] at hh
      exact (by decide : 576774792492622 % 1919519569386763 ≠ 1 % 1919519569386763) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((1919519569386763-1)/8574133) 1919519569386763 256) 1 1919519569386763).mp heq
      rw [exp_1919519569386763_7] at hh
      exact (by decide : 1059928654987441 % 1919519569386763 ≠ 1 % 1919519569386763) hh
#print axioms prime_1919519569386763
theorem exp_2437_0 : modPow 2 2436 2437 256 = 1 := by decide +kernel
#print axioms exp_2437_0
theorem exp_2437_1 : modPow 2 1218 2437 256 = 2436 := by decide +kernel
#print axioms exp_2437_1
theorem exp_2437_2 : modPow 2 812 2437 256 = 2351 := by decide +kernel
#print axioms exp_2437_2
theorem exp_2437_3 : modPow 2 348 2437 256 = 801 := by decide +kernel
#print axioms exp_2437_3
theorem exp_2437_4 : modPow 2 84 2437 256 = 433 := by decide +kernel
#print axioms exp_2437_4
theorem prime_2437 : Nat.Prime 2437 := by
  apply certificate 2437 2 256 (by decide) [2, 2, 3, 7, 29]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_7 | exact prime_29
  · decide
  · exact exp_2437_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((2437-1)/2) 2437 256) 1 2437).mp heq
      rw [exp_2437_1] at hh
      exact (by decide : 2436 % 2437 ≠ 1 % 2437) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((2437-1)/2) 2437 256) 1 2437).mp heq
      rw [exp_2437_1] at hh
      exact (by decide : 2436 % 2437 ≠ 1 % 2437) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((2437-1)/3) 2437 256) 1 2437).mp heq
      rw [exp_2437_2] at hh
      exact (by decide : 2351 % 2437 ≠ 1 % 2437) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((2437-1)/7) 2437 256) 1 2437).mp heq
      rw [exp_2437_3] at hh
      exact (by decide : 801 % 2437 ≠ 1 % 2437) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((2437-1)/29) 2437 256) 1 2437).mp heq
      rw [exp_2437_4] at hh
      exact (by decide : 433 % 2437 ≠ 1 % 2437) hh
#print axioms prime_2437
theorem prime_97 : Nat.Prime 97 := by norm_num
#print axioms prime_97
theorem prime_419 : Nat.Prime 419 := by norm_num
#print axioms prime_419
theorem exp_569003_0 : modPow 2 569002 569003 256 = 1 := by decide +kernel
#print axioms exp_569003_0
theorem exp_569003_1 : modPow 2 284501 569003 256 = 569002 := by decide +kernel
#print axioms exp_569003_1
theorem exp_569003_2 : modPow 2 81286 569003 256 = 450780 := by decide +kernel
#print axioms exp_569003_2
theorem exp_569003_3 : modPow 2 5866 569003 256 = 439588 := by decide +kernel
#print axioms exp_569003_3
theorem exp_569003_4 : modPow 2 1358 569003 256 = 236160 := by decide +kernel
#print axioms exp_569003_4
theorem prime_569003 : Nat.Prime 569003 := by
  apply certificate 569003 2 256 (by decide) [2, 7, 97, 419]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_7 | exact prime_97 | exact prime_419
  · decide
  · exact exp_569003_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((569003-1)/2) 569003 256) 1 569003).mp heq
      rw [exp_569003_1] at hh
      exact (by decide : 569002 % 569003 ≠ 1 % 569003) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((569003-1)/7) 569003 256) 1 569003).mp heq
      rw [exp_569003_2] at hh
      exact (by decide : 450780 % 569003 ≠ 1 % 569003) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((569003-1)/97) 569003 256) 1 569003).mp heq
      rw [exp_569003_3] at hh
      exact (by decide : 439588 % 569003 ≠ 1 % 569003) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((569003-1)/419) 569003 256) 1 569003).mp heq
      rw [exp_569003_4] at hh
      exact (by decide : 236160 % 569003 ≠ 1 % 569003) hh
#print axioms prime_569003
theorem exp_2773320623_0 : modPow 5 2773320622 2773320623 256 = 1 := by decide +kernel
#print axioms exp_2773320623_0
theorem exp_2773320623_1 : modPow 5 1386660311 2773320623 256 = 2773320622 := by decide +kernel
#print axioms exp_2773320623_1
theorem exp_2773320623_2 : modPow 5 1138006 2773320623 256 = 844634197 := by decide +kernel
#print axioms exp_2773320623_2
theorem exp_2773320623_3 : modPow 5 4874 2773320623 256 = 2420059583 := by decide +kernel
#print axioms exp_2773320623_3
theorem prime_2773320623 : Nat.Prime 2773320623 := by
  apply certificate 2773320623 5 256 (by decide) [2, 2437, 569003]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_2437 | exact prime_569003
  · decide
  · exact exp_2773320623_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((2773320623-1)/2) 2773320623 256) 1 2773320623).mp heq
      rw [exp_2773320623_1] at hh
      exact (by decide : 2773320622 % 2773320623 ≠ 1 % 2773320623) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((2773320623-1)/2437) 2773320623 256) 1 2773320623).mp heq
      rw [exp_2773320623_2] at hh
      exact (by decide : 844634197 % 2773320623 ≠ 1 % 2773320623) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 5 ((2773320623-1)/569003) 2773320623 256) 1 2773320623).mp heq
      rw [exp_2773320623_3] at hh
      exact (by decide : 2420059583 % 2773320623 ≠ 1 % 2773320623) hh
#print axioms prime_2773320623
theorem exp_72106336199_0 : modPow 7 72106336198 72106336199 256 = 1 := by decide +kernel
#print axioms exp_72106336199_0
theorem exp_72106336199_1 : modPow 7 36053168099 72106336199 256 = 72106336198 := by decide +kernel
#print axioms exp_72106336199_1
theorem exp_72106336199_2 : modPow 7 5546641246 72106336199 256 = 58700762603 := by decide +kernel
#print axioms exp_72106336199_2
theorem exp_72106336199_3 : modPow 7 26 72106336199 256 = 28357292573 := by decide +kernel
#print axioms exp_72106336199_3
theorem prime_72106336199 : Nat.Prime 72106336199 := by
  apply certificate 72106336199 7 256 (by decide) [2, 13, 2773320623]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_13 | exact prime_2773320623
  · decide
  · exact exp_72106336199_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((72106336199-1)/2) 72106336199 256) 1 72106336199).mp heq
      rw [exp_72106336199_1] at hh
      exact (by decide : 72106336198 % 72106336199 ≠ 1 % 72106336199) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((72106336199-1)/13) 72106336199 256) 1 72106336199).mp heq
      rw [exp_72106336199_2] at hh
      exact (by decide : 58700762603 % 72106336199 ≠ 1 % 72106336199) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((72106336199-1)/2773320623) 72106336199 256) 1 72106336199).mp heq
      rw [exp_72106336199_3] at hh
      exact (by decide : 28357292573 % 72106336199 ≠ 1 % 72106336199) hh
#print axioms prime_72106336199
theorem exp_75445702479781427272750846543864801_0 : modPow 7 75445702479781427272750846543864800 75445702479781427272750846543864801 256 = 1 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_0
theorem exp_75445702479781427272750846543864801_1 : modPow 7 37722851239890713636375423271932400 75445702479781427272750846543864801 256 = 75445702479781427272750846543864800 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_1
theorem exp_75445702479781427272750846543864801_2 : modPow 7 25148567493260475757583615514621600 75445702479781427272750846543864801 256 = 17027744575660264744512945715121884 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_2
theorem exp_75445702479781427272750846543864801_3 : modPow 7 15089140495956285454550169308772960 75445702479781427272750846543864801 256 = 52755092631156469601217826477970212 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_3
theorem exp_75445702479781427272750846543864801_4 : modPow 7 996548568557483816196003626400 75445702479781427272750846543864801 256 = 57103426308028043857659793617446015 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_4
theorem exp_75445702479781427272750846543864801_5 : modPow 7 1046311689884858398375200 75445702479781427272750846543864801 256 = 72344277920069036431504068385047591 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_5
theorem exp_75445702479781427272750846543864801_6 : modPow 7 39304471641247389600 75445702479781427272750846543864801 256 = 33763476511538335360127990623883028 := by decide +kernel
#print axioms exp_75445702479781427272750846543864801_6
theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 := by
  apply certificate 75445702479781427272750846543864801 7 256 (by decide) [2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 1919519569386763, 72106336199]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_5 | exact prime_75707 | exact prime_72106336199 | exact prime_1919519569386763
  · decide
  · exact exp_75445702479781427272750846543864801_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/2) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_1] at hh
      exact (by decide : 75445702479781427272750846543864800 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/2) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_1] at hh
      exact (by decide : 75445702479781427272750846543864800 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/2) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_1] at hh
      exact (by decide : 75445702479781427272750846543864800 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/2) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_1] at hh
      exact (by decide : 75445702479781427272750846543864800 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/2) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_1] at hh
      exact (by decide : 75445702479781427272750846543864800 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/3) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_2] at hh
      exact (by decide : 17027744575660264744512945715121884 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/3) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_2] at hh
      exact (by decide : 17027744575660264744512945715121884 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/5) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_3] at hh
      exact (by decide : 52755092631156469601217826477970212 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/5) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_3] at hh
      exact (by decide : 52755092631156469601217826477970212 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/75707) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_4] at hh
      exact (by decide : 57103426308028043857659793617446015 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/1919519569386763) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_6] at hh
      exact (by decide : 33763476511538335360127990623883028 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 7 ((75445702479781427272750846543864801-1)/72106336199) 75445702479781427272750846543864801 256) 1 75445702479781427272750846543864801).mp heq
      rw [exp_75445702479781427272750846543864801_5] at hh
      exact (by decide : 72344277920069036431504068385047591 % 75445702479781427272750846543864801 ≠ 1 % 75445702479781427272750846543864801) hh
#print axioms prime_75445702479781427272750846543864801
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_0 : modPow 2 74058212732561358302231226437062788676166966415465897661863160754340906 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 1 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_0
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_1 : modPow 2 37029106366280679151115613218531394338083483207732948830931580377170453 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 74058212732561358302231226437062788676166966415465897661863160754340906 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_1
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_2 : modPow 2 24686070910853786100743742145687596225388988805155299220621053584780302 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 30397109428614726089754189191956088611235801571633239974164411255784155 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_2
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_3 : modPow 2 209796636636151156663544550813209033076960244803019540118592523383402 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 8562916886866218785688304546164188478888058893729309188831496247839076 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_3
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_4 : modPow 2 1288708523719027586305727224964984924846728842909250485702458119518 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 34423717228876157273670922671787235583289084632054732964365754153055025 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_4
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_5 : modPow 2 560838875966961948233089432233964578877287722099113947563882806794 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 54871647690314810166557542068595163151590274869528630571075996285882505 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_5
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_6 : modPow 2 38509147694185143878364744631319200843710219946028640589009268082 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 52266576830164329332527201090776533817489900267135412990654516667243924 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_6
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_7 : modPow 2 2331972502653487852620185443007392165117953542933313402 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 50366660687963342066214195241331738400016478712605795091965648721912165 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_7
theorem exp_74058212732561358302231226437062788676166966415465897661863160754340907_8 : modPow 2 981609426360740691344999861639072106 74058212732561358302231226437062788676166966415465897661863160754340907 256 = 69490809710348678725736597923071784769591275419387514694139338586948360 := by decide +kernel
#print axioms exp_74058212732561358302231226437062788676166966415465897661863160754340907_8
theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 := by
  apply certificate 74058212732561358302231226437062788676166966415465897661863160754340907 2 256 (by decide) [2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_353 | exact prime_57467 | exact prime_132049 | exact prime_1923133 | exact prime_31757755568855353 | exact prime_75445702479781427272750846543864801
  · decide
  · exact exp_74058212732561358302231226437062788676166966415465897661863160754340907_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/2) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_1] at hh
      exact (by decide : 74058212732561358302231226437062788676166966415465897661863160754340906 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/3) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_2] at hh
      exact (by decide : 30397109428614726089754189191956088611235801571633239974164411255784155 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/353) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_3] at hh
      exact (by decide : 8562916886866218785688304546164188478888058893729309188831496247839076 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/57467) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_4] at hh
      exact (by decide : 34423717228876157273670922671787235583289084632054732964365754153055025 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/132049) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_5] at hh
      exact (by decide : 54871647690314810166557542068595163151590274869528630571075996285882505 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/1923133) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_6] at hh
      exact (by decide : 52266576830164329332527201090776533817489900267135412990654516667243924 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/31757755568855353) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_7] at hh
      exact (by decide : 50366660687963342066214195241331738400016478712605795091965648721912165 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((74058212732561358302231226437062788676166966415465897661863160754340907-1)/75445702479781427272750846543864801) 74058212732561358302231226437062788676166966415465897661863160754340907 256) 1 74058212732561358302231226437062788676166966415465897661863160754340907).mp heq
      rw [exp_74058212732561358302231226437062788676166966415465897661863160754340907_8] at hh
      exact (by decide : 69490809710348678725736597923071784769591275419387514694139338586948360 % 74058212732561358302231226437062788676166966415465897661863160754340907 ≠ 1 % 74058212732561358302231226437062788676166966415465897661863160754340907) hh
#print axioms prime_74058212732561358302231226437062788676166966415465897661863160754340907
theorem exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_0 : modPow 2 57896044618658097711785492504343953926634992332820282019728792003956564819948 57896044618658097711785492504343953926634992332820282019728792003956564819949 256 = 1 := by decide +kernel
#print axioms exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_0
theorem exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_1 : modPow 2 28948022309329048855892746252171976963317496166410141009864396001978282409974 57896044618658097711785492504343953926634992332820282019728792003956564819949 256 = 57896044618658097711785492504343953926634992332820282019728792003956564819948 := by decide +kernel
#print axioms exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_1
theorem exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_2 : modPow 2 19298681539552699237261830834781317975544997444273427339909597334652188273316 57896044618658097711785492504343953926634992332820282019728792003956564819949 256 = 25380276437079137597092236364571181010632177832931468165172742469126098314552 := by decide +kernel
#print axioms exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_2
theorem exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_3 : modPow 2 888698552790736299626774717244753464114003596985590771942357929052090884 57896044618658097711785492504343953926634992332820282019728792003956564819949 256 = 22602559476203468486837656474023958799180643873278202064348025470901666305470 := by decide +kernel
#print axioms exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_3
theorem exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_4 : modPow 2 781764 57896044618658097711785492504343953926634992332820282019728792003956564819949 256 = 427094198651976259540344842774561673889945192655078505504941250475370961481 := by decide +kernel
#print axioms exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_4
theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  apply certificate 57896044618658097711785492504343953926634992332820282019728792003956564819949 2 256 (by decide) [2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_65147 | exact prime_74058212732561358302231226437062788676166966415465897661863160754340907
  · decide
  · exact exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_0
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949-1)/2) 57896044618658097711785492504343953926634992332820282019728792003956564819949 256) 1 57896044618658097711785492504343953926634992332820282019728792003956564819949).mp heq
      rw [exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_1] at hh
      exact (by decide : 57896044618658097711785492504343953926634992332820282019728792003956564819948 % 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≠ 1 % 57896044618658097711785492504343953926634992332820282019728792003956564819949) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949-1)/2) 57896044618658097711785492504343953926634992332820282019728792003956564819949 256) 1 57896044618658097711785492504343953926634992332820282019728792003956564819949).mp heq
      rw [exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_1] at hh
      exact (by decide : 57896044618658097711785492504343953926634992332820282019728792003956564819948 % 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≠ 1 % 57896044618658097711785492504343953926634992332820282019728792003956564819949) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949-1)/3) 57896044618658097711785492504343953926634992332820282019728792003956564819949 256) 1 57896044618658097711785492504343953926634992332820282019728792003956564819949).mp heq
      rw [exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_2] at hh
      exact (by decide : 25380276437079137597092236364571181010632177832931468165172742469126098314552 % 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≠ 1 % 57896044618658097711785492504343953926634992332820282019728792003956564819949) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949-1)/65147) 57896044618658097711785492504343953926634992332820282019728792003956564819949 256) 1 57896044618658097711785492504343953926634992332820282019728792003956564819949).mp heq
      rw [exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_3] at hh
      exact (by decide : 22602559476203468486837656474023958799180643873278202064348025470901666305470 % 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≠ 1 % 57896044618658097711785492504343953926634992332820282019728792003956564819949) hh
    · intro heq
      have hh := (ZMod.natCast_eq_natCast_iff' (modPow 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949-1)/74058212732561358302231226437062788676166966415465897661863160754340907) 57896044618658097711785492504343953926634992332820282019728792003956564819949 256) 1 57896044618658097711785492504343953926634992332820282019728792003956564819949).mp heq
      rw [exp_57896044618658097711785492504343953926634992332820282019728792003956564819949_4] at hh
      exact (by decide : 427094198651976259540344842774561673889945192655078505504941250475370961481 % 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≠ 1 % 57896044618658097711785492504343953926634992332820282019728792003956564819949) hh
#print axioms prime_57896044618658097711785492504343953926634992332820282019728792003956564819949
end AspisR1.JHt_Prime
