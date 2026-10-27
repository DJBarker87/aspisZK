"""Tiny compile-free arithmetic check of retained R002 limbs; no inverse evaluation.
Kernel authority remains the retained generic source-execution/fallback theorems.
"""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
P=2147483647

def cm_add(x,y):return tuple((a+b)%P for a,b in zip(x,y))
def cm_neg(x):return tuple(-a%P for a in x)
def cm_mul(x,y):
 a,b=x;c,d=y
 return ((a*c-b*d)%P,(a*d+b*c)%P)
def add(x,y):return tuple((a+b)%P for a,b in zip(x,y))
def neg(x):return tuple(-a%P for a in x)
def mul(x,y):
 a,b=x[:2],x[2:];c,d=y[:2],y[2:]
 return cm_add(cm_mul(a,c),cm_mul((2,1),cm_mul(b,d)))+cm_add(cm_mul(a,d),cm_mul(b,c))
ONE=(1,0,0,0)
probe=E.parent/'leaf-p6-13-20261027/LPo_R002/stdout.log'
rows=[]
for line in probe.read_text().splitlines():
 if not line.startswith('row='):continue
 row=int(line.split()[0].split('=')[1]);t=(row,0,1,0)
 vals={name:tuple(map(int,nums.split(','))) for name,nums in re.findall(r'(native_[xy])=\[([^]]+)\]',line)}
 x,y=vals['native_x'],vals['native_y'];square=mul(t,t);den=add(ONE,square)
 checks={'canonical':all(0<=n<P for n in x+y),'denominator_nonzero':any(den),'x_times_denominator':mul(x,den)==add(ONE,neg(square)),'y_times_denominator':mul(y,den)==add(t,t)}
 assert all(checks.values()),checks
 rows.append(dict(row=row,parameter=t,native_x=x,native_y=y,denominator=den,checks=checks,adopted_result='Aeneas.Std.Result.ok (fromR72Point (encodePoint (point parameter)))',numeric_comparison='same canonical coordinates by denominator products; compile-free fixture, not a fresh kernel theorem'))
report={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'R002_stdout_sha256':hashlib.sha256(probe.read_bytes()).hexdigest(),'rows':rows,'new_rust_runs':0,'new_kani_runs':0,'axioms':'N/A: Python fixture; generic Lean theorems reused separately'}
(E/'CDX_native-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print('Both R002 rows satisfy the adopted rational-map equations; all limbs canonical.')
