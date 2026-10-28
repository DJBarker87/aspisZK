import R1Z.GamesR1PBin
import R1Z.ReadBudgetR1

/-! Exact binary attempt size and the existing D76 error bound. The two
binding reads are included, in addition to CommitReadsR1's Mc. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.GamesR1PBin
open R0P R0Z.FsStatement R0Z.HvzkV R1Z.GamesR1 R1Z.CommitReadsR1

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)

theorem n1_eq : n1 W Pr = 115 + (McR1 Pr.E₁ Pr.E₂ + 2) := by
  rw [n1, card_Pos1]
  unfold McR1
  omega

theorem n1_worst_case (h₁ : Pr.E₁ = 90112) (h₂ : Pr.E₂ = 8192) :
    n1 W Pr = 2457717 := by rw [n1_eq, h₁, h₂]; rfl

/-- Source counts plus expander budgets, including both binding reads. -/
theorem n1_le (L₁ L₂ : ℕ) (hc : RCommitCount L₁ L₂)
    (h₁ : Pr.E₁ ≤ 2 * L₁) (h₂ : Pr.E₂ ≤ 2 * L₂) : n1 W Pr ≤ 2 ^ 22 := by
  rw [n1_eq]
  obtain ⟨hc₁, hc₂⟩ := hc
  unfold McR1
  norm_num at *
  omega

/-- Exactly the error expression in the binary phase-indexed privacy root.
The existing ReadBudgetR1 theorem is instantiated, not modified. -/
theorem binary_games_error_le (L₁ L₂ qmax : ℕ) (εexh : ℚ)
    (hc : RCommitCount L₁ L₂) (h₁ : Pr.E₁ ≤ 2 * L₁) (h₂ : Pr.E₂ ≤ 2 * L₂)
    (hq : qmax ≤ 2 ^ 64) (he : εexh ≤ 1 / 2 ^ 229) :
    ((8 * n1 W Pr : ℕ) : ℚ) * (qmax : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
      (((8 * n1 W Pr : ℕ) : ℚ) * ((8 * n1 W Pr : ℕ) : ℚ) /
        ((2 ^ 255 : ℕ) : ℚ) + εexh) +
      ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
      (8 : ℚ) * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ)) ≤
        1 / 2 ^ 109 + 1 / 2 ^ 137 := by
  rw [n1_eq]
  exact R1Z.ReadBudgetR1.r1_games_error_le _ qmax εexh
    (by rw [← n1_eq W Pr]; exact n1_le W Pr L₁ L₂ hc h₁ h₂) hq he

#print axioms n1_eq
#print axioms n1_worst_case
#print axioms n1_le
#print axioms binary_games_error_le
end R1Z.GamesR1PBin
