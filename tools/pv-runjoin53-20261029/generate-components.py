from pathlib import Path
import importlib.util
T=Path(__file__).parent
sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
for tag,op,scalar in [('CAdd','add','AddCanon'),('CSub','sub','Sub')]:
 body=f'''open PV_RunJoin_CircleNeutralShape53

theorem complete (a b : U32 × U32) (ha : CC a) (hb : CC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.{op} a b = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.{op} a b = ok y ∧ CC y := by
  obtain ⟨y0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutral{scalar}53.complete a.1 b.1 ha.1 hb.1
  obtain ⟨y1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutral{scalar}53.complete a.2 b.2 ha.2 hb.2
  refine ⟨(y0,y1),?_,?_,hc0,hc1⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.{op}
    simp only [h0,h1,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.CM31.{op}
    simp only [h0',h1',bind_tc_ok]
'''
 w.write('PV_RunJoin_CircleNeutral'+tag+'53',['R1Z.PV_RunJoin_CircleNeutral'+scalar+'53'],body,['complete'])
 body=body.replace('U32 × U32','(U32 × U32) × (U32 × U32)').replace('CC','QC').replace('field.CM31','field.QM31').replace('ha.1 hb.1','ha.1 hb.1').replace('PV_RunJoin_CircleNeutral'+scalar+'53','PV_RunJoin_CircleNeutral'+tag+'53')
 w.write('PV_RunJoin_CircleNeutralQ'+op.capitalize()+'53',['R1Z.PV_RunJoin_CircleNeutral'+tag+'53'],body,['complete'])
body='''open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32 × U32) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.neg a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.neg a = ok y ∧ CC y := by
  obtain ⟨y0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralNeg53.complete a.1 ha.1
  obtain ⟨y1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralNeg53.complete a.2 ha.2
  refine ⟨(y0,y1),?_,?_,hc0,hc1⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.neg
    simp only [h0,h1,bind_tc_ok]
  · unfold PV_RunJoin_CircleR72Raw52.field.CM31.neg
    simp only [h0',h1',bind_tc_ok]
'''
w.write('PV_RunJoin_CircleNeutralCNeg53',['R1Z.PV_RunJoin_CircleNeutralNeg53'],body,['complete'])
w.write('PV_RunJoin_CircleNeutralCDouble53',['R1Z.PV_RunJoin_CircleNeutralCAdd53'],'''open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32 × U32) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.double a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.double a = ok y ∧ CC y :=
  PV_RunJoin_CircleNeutralCAdd53.complete a a ha ha
''',['complete'])
