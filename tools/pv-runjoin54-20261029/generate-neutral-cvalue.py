from pathlib import Path
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
for name,op,model in [('Add','add','ca'),('Sub','sub','cs')]:
 stem='PV_RunJoin_NeutralC'+name+'Value54'
 s=f'''import R1Z.PV_RunJoin_NeutralTowerValue54
import R1Z.PV_RunJoin_Neutral{name}Value54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.{stem}
open PV_RunJoin_NeutralValue54 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53
theorem complete (a b : C) (ha : CC a) (hb : CC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.{op} a b=ok y ∧ CC y ∧ cv y={model} (cv a) (cv b) := by
  obtain ⟨y0,h0,hc0,hv0⟩ := PV_RunJoin_Neutral{name}Value54.complete a.1 b.1 ha.1 hb.1
  obtain ⟨y1,h1,hc1,hv1⟩ := PV_RunJoin_Neutral{name}Value54.complete a.2 b.2 ha.2 hb.2
  refine ⟨(y0,y1),?_,⟨hc0,hc1⟩,?_⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.{op}
    simp only [h0,h1,bind_tc_ok]
  · exact Prod.ext hv0 hv1
#print axioms complete
end R1Z.{stem}
''';(L/(stem+'.lean')).write_text(s)
