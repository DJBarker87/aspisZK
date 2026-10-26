from pathlib import Path
import re,json
L=Path('lean'); E=Path('evidence/finish-local-20261026')
# One atomic inventory per independently relevant boundary, reusing Rc9's checked inventory selection.
mods=[]
mp={'AspisR1.SAF_C_SAF_FinishPrepared.Outcome':'AspisR1.FIs_Finish.Outcome','AspisR1.SAF_ReducedLaws.Arithmetic':'AspisR1.FIs_Pair.Law','AspisR1.Rc5_Cont.Outcome':'AspisR1.FIs_Cont.Outcome','AspisR1.Rc5_Literal.Outcome':'AspisR1.FIs_Literal.Outcome','AspisR1.P2P_Result.Outcome':'AspisR1.FIs_Result.Outcome','AspisR1.P2P_Caller.Outcome':'AspisR1.FIs_Caller.Outcome','AspisR1.Rc9_Top.deployed':'AspisR1.FIs_Top.deployed','AspisR1.Rc9_Nonvacuity.composed':'AspisR1.FIs_Nonvacuity.composed'}
for p in sorted(L.glob('Rc9_Audit*.lean')):
 s=p.read_text(); s='import FIs_Top\nimport FIs_Nonvacuity\n'+s
 for old,new in mp.items():s=s.replace(old,new)
 name=p.stem.replace('Rc9_','FIs_');(L/(name+'.lean')).write_text(s);mods.append(name)
(E/'FIs_audit_plan.json').write_text(json.dumps(mods,indent=2)+'\n')
s='''import Rc9_Top
import FIs_Top
import FIs_Nonvacuity
set_option pp.all false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.explicit false
set_option pp.universes false
set_option format.width 140
#check @AspisR1.Rc9_Top.deployed
#check @AspisR1.FIs_Top.deployed
#check @AspisR1.FIs_Nonvacuity.composed
#print axioms AspisR1.FIs_Top.deployed
#print axioms AspisR1.FIs_Nonvacuity.composed
''';(L/'FIs_Statements.lean').write_text(s)
