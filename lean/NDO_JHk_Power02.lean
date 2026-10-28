import RPt_JFq_Rho
import RPt_JFq_Power
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Power02
open CheckpointBytes5Output (ofK)
def value : OraclePortCheckpointAbiC5.K := ⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩
/-- One field multiplication, with concrete operands; no recurrence unfolds. -/
theorem step : CheckpointBytes5Output.ofK JFq_Rho.scalar * CheckpointBytes5Output.ofK JFq_Rho.scalar=value := by
  change (⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩ : OraclePortCheckpointAbiC5.K) * ⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩=⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : ofK JFq_Rho.scalar^2=value := by
  rw [pow_two]
  exact step
#print axioms source
end AspisR1.JHk_Power02
end
