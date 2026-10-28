import NDO_JHk_Power04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Power08
open CheckpointBytes5Output (ofK)
def value : OraclePortCheckpointAbiC5.K := ⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩
/-- One field multiplication, with concrete operands; no recurrence unfolds. -/
theorem step : JHk_Power04.value * JHk_Power04.value=value := by
  change (⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩ : OraclePortCheckpointAbiC5.K) * ⟨⟨167538953,1037266155⟩,⟨1493695586,2009572989⟩⟩=⟨⟨394857433,485124437⟩,⟨1298755794,351690291⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : ofK JFq_Rho.scalar^8=value := by
  rw [show 8=(4:Nat)+4 from rfl,pow_add,JHk_Power04.source]
  exact step
#print axioms source
end AspisR1.JHk_Power08
end
