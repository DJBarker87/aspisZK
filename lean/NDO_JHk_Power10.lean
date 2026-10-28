import NDO_JHk_Power08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Power10
open CheckpointBytes5Output (ofK)
def value : OraclePortCheckpointAbiC5.K := ⟨⟨1007926423,526023474⟩,⟨347718395,268326460⟩⟩
/-- One field multiplication, with concrete operands; no recurrence unfolds. -/
theorem step : JHk_Power08.value * JHk_Power02.value=value := by
  change (⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩ : OraclePortCheckpointAbiC5.K) * ⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩=⟨⟨1007926423,526023474⟩,⟨347718395,268326460⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : ofK JFq_Rho.scalar^10=value := by
  rw [show 10=(8:Nat)+2 from rfl,pow_add,JHk_Power08.source,JHk_Power02.source]
  exact step
#print axioms source
theorem retained : ofK JFq_Rho.scalar^10=ofK JFq_Power.scalar :=
  source
#print axioms retained
end AspisR1.JHk_Power10
end
