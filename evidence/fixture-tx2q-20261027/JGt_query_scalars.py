"""Generate bounded proposed scalar computations for SAME query rhs/power.
These modules do not claim the full dot gate. Compile before crediting them.
"""
from pathlib import Path
import json,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
x={"__file__":str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')}
exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
d=json.loads((P/'JGt_DOT_PREFLIGHT.json').read_text());w=x['wide'];mul=x['mul']
def q(v):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(v)
for i in range(12):
 m=f'JGt_QueryScalars{i}';prev=f'JGt_QueryScalars{i-1}';state=d['states'][i];out=d['states'][i+1];product=mul(d['lines'][i],state['power']+[0]*4)
 h='import JFz_TX2_Gates\nimport JFn_QueryArithmeticTotal\n' if i==0 else 'import '+prev+'\n'
 s=h+f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{m}
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
'''
 if i==0:s+=f'def beforeRhs : E := {w(state["rhs"])}\ndef beforePower : K := {q(state["power"])}\n'
 else:s+=f'abbrev beforeRhs := {prev}.rhs\nabbrev beforePower := {prev}.power\n'
 s+=f'''def product : E := {w(product)}
def rhs : E := {w(out['rhs'])}
def power : K := {q(out['power'])}
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨{i},by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.{m}
end
'''
 p=P/'JGt_UNCHECKED'/(m+'.lean.txt')
 if '--check' in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
print('12 proposed sequential query scalar modules')
