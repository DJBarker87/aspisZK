from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent
p=2147483647
add=lambda a,b:tuple((x+y)%p for x,y in zip(a,b))
sub=lambda a,b:tuple((x-y)%p for x,y in zip(a,b))
def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def mul(a,b):
 c=cm(a[:2],b[:2]);d=cm(a[2:],b[2:]);dr=cm(d,(2,1));e=cm(a[:2],b[2:]);f=cm(a[2:],b[:2]);return add(c,dr)+add(e,f)
def lit(a):return '⟨⟨'+','.join(map(str,a[:2]))+'⟩,⟨'+','.join(map(str,a[2:]))+'⟩⟩'
header='''import JFu_CircleExact
import JFq_Z0
import JFq_Z1
import JFq_Z2
import JFq_Z3
set_option autoImplicit false
noncomputable section
'''
files={};rows=[]
for j,t in enumerate([(816245010,114551508,1501205590,2011200735),(758445278,139479390,789205686,1156709222)]):
 sq=mul(t,t);den=add((1,0,0,0),sq)
 vals=[]
 for k in range(2):
  s=(R/f'lean/JFq_Z{2*j+k}.lean').read_text();vals.append(tuple(map(int,re.findall(r'(\d+)#u32',s.split('def decoded :')[1].split('\ntheorem decode')[0]))))
 assert mul(vals[0],den)==sub((1,0,0,0),sq)
 assert mul(vals[1],den)==add(t,t)
 rows.append(dict(point=j,parameter=t,square=sq,denominator=den,x=vals[0],y=vals[1]))
 name=f'JHl_Z{j}Square'
 files[name]=header+f'''namespace AspisR1.{name}
open AspisV8R15.ExactTowerBase
def square : QM31Exact := {lit(sq)}
def denominator : QM31Exact := {lit(den)}
theorem source : JFu_CircleParameters.t{25+j}^2=square := by
  rw [pow_two]
  change ({lit(t)} : QM31Exact)*{lit(t)}={lit(sq)}
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
theorem den : 1+JFu_CircleParameters.t{25+j}^2=denominator := by
  rw [source]
  change (1 : QM31Exact)+{lit(sq)}={lit(den)}
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms den
end AspisR1.{name}
end
'''
 for k in range(2):
  name=f'JHl_Z{j}'+('X' if k==0 else 'Y')
  rhs=f'(1 : QM31Exact)-JHl_Z{j}Square.square' if k==0 else f'2*JFu_CircleParameters.t{25+j}'
  files[name]=f'import JHl_Z{j}Square\n'+header+f'''namespace AspisR1.{name}
open AspisV8R15.ExactTowerBase
def value : QM31Exact := {lit(vals[k])}
theorem source : value*JHl_Z{j}Square.denominator={rhs} := by
  change ({lit(vals[k])} : QM31Exact)*{lit(den)}='''+(f'(1 : QM31Exact)-{lit(sq)}' if k==0 else f'(2 : QM31Exact)*{lit(t)}')+f'''
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
end AspisR1.{name}
end
'''
for name,s in files.items():
 # imports precede commands
 if 'end\nimport' in s:raise AssertionError(name)
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
(P/'JHl_Z_PREFLIGHT.json').write_text(json.dumps(rows,indent=2)+'\n')
print('6 bounded circle certificates validated')
