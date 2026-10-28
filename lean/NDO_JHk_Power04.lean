import NDO_JHk_Power02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Power04
open CheckpointBytes5Output (ofK)
def value : OraclePortCheckpointAbiC5.K := ⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩
/-- One field multiplication, with concrete operands; no recurrence unfolds. -/
theorem step : JHk_Power02.value * JHk_Power02.value=value := by
  change (⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩ : OraclePortCheckpointAbiC5.K) * ⟨⟨823287192,1866424561⟩,⟨1944788384,1773633471⟩⟩=⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : ofK JFq_Rho.scalar^4=value := by
  rw [show 4=(2:Nat)+2 from rfl,pow_add,JHk_Power02.source]
  exact step
#print axioms source
end AspisR1.JHk_Power04
end
