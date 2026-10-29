import R1Z.PV_RunJoin_R24Canonical54
import R1Z.PV_RunJoin_R24Value0_54
import R1Z.PV_RunJoin_R24Value1_54
import R1Z.PV_RunJoin_R24Value2_54
import R1Z.PV_RunJoin_R24Value3_54
import R1Z.PV_RunJoin_NeutralQMulValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Complete54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_NeutralValue54

theorem complete (a b : Q) (ha : QC a) (hb : QC b) :
    ∃ y, PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul a b=ok (some y) ∧
      PV_RunJoin_CircleRawTower52.field.QM31.mul a b=ok y ∧ QC y := by
  obtain ⟨y,hy,hcy,h0,h1,h2,h3⟩ := PV_RunJoin_R24Canonical54.complete a b ha hb
  obtain ⟨z,hz,hcz,hvz⟩ := PV_RunJoin_NeutralQMulValue54.complete a b ha hb
  have hvy : qv y=qm (qv a) (qv b) := by
    apply Prod.ext <;> apply Prod.ext
    · exact (residue _ _ h0).trans (PV_RunJoin_R24Value0_54.complete a b ha hb)
    · exact (residue _ _ h1).trans (PV_RunJoin_R24Value1_54.complete a b ha hb)
    · exact (residue _ _ h2).trans (PV_RunJoin_R24Value2_54.complete a b ha hb)
    · exact (residue _ _ h3).trans (PV_RunJoin_R24Value3_54.complete a b ha hb)
  have he : y=z := qi _ _ hcy hcz (hvy.trans hvz.symm)
  exact ⟨y,hy,he.symm ▸ hz,hcy⟩

#print axioms complete
end R1Z.PV_RunJoin_R24Complete54
