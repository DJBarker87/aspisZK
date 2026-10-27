from pathlib import Path
import json,sys
def emit(path,text):
 p=Path(path)
 if "--check" in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
v=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_NUMERIC_PREFLIGHT.json').read_text())['dots']
def rec(xs):
 if len(xs)==1:return str(xs[0])
 n=len(xs)//2;return '⟨'+rec(xs[:n])+','+rec(xs[n:])+'⟩'
s='''import JFw_TX2_CircleNumbers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFw_TX2_CircleNumbers
'''
for k in range(4):s+=f'def d{k} : FE := JFw_TX2_PowersExplicit.decode JFw_TX2_Dot{k}.value\n'
exprs=['(d0+d1+d2+d3)*536870912','(d0-d1-d2+d3)*(536870912*1029545577)','(d0+d1-d2-d3)*(536870912*243259912)','(d0-d1+d2-d3)*(536870912*243259912*1029545577)']
for k,expr in enumerate(exprs):
 s+=f'''theorem coefficient{k} : {expr}=h{k} := by
  change ({expr.replace('d0',rec(v[0])).replace('d1',rec(v[1])).replace('d2',rec(v[2])).replace('d3',rec(v[3]))} : FE)=h{k}
  unfold h{k}
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
'''
s+='''#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFw_TX2_CircleCoefficients
end
'''
emit('lean/JFw_TX2_CircleCoefficients.lean',s)
