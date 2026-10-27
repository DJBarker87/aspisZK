from pathlib import Path
import json,sys
def emit(path,text):
 p=Path(path)
 if "--check" in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
P=2147483647
v=json.loads(Path('evidence/fixture-tx2g-20261026/JFw_NUMERIC_PREFLIGHT.json').read_text())['dots']
A=[492967452,709301790,1617612614,599334322,1668486716,1253062525,341779229,880523595];ix=243259912;iy=1029545577;q=536870912
# Local small arithmetic only; numeric proposals become checked equations in Lean.
def rec(xs):
 if len(xs)==1:return str(xs[0])
 n=len(xs)//2;return '⟨'+rec(xs[:n])+','+rec(xs[n:])+'⟩'
def add(a,b):return [(x+y)%P for x,y in zip(a,b)]
def mul(a,b):
 if len(a)==1:return [a[0]*b[0]%P]
 n=len(a)//2;hi=mul(a[n:],b[n:]);r=[-hi[0]%P] if n==1 else mul(hi,[2,1] if n==2 else [0,0,1,0])
 return add(mul(a[:n],b[:n]),r)+add(mul(a[:n],b[n:]),mul(a[n:],b[:n]))
H=[]
for signs,scale in [([1,1,1,1],q),([1,-1,-1,1],q*iy%P),([1,1,-1,-1],q*ix%P),([1,-1,1,-1],q*ix*iy%P)]:
 H.append([sum(signs[s]*v[s][j] for s in range(4))*scale%P for j in range(8)])
T2=add(H[2],mul(A,H[3]));T1=add(H[1],mul(A,T2));O=add(H[0],mul(A,T1))
head='''import JFw_TX2_Dots0
import JFv_TX2_Query0Formula
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
'''
head+=f'def alpha : FE := {rec(A)}\n'
for k in range(4):head+=f'def h{k} : FE := {rec(H[k])}\n'
head+=f'def t2 : FE := {rec(T2)}\ndef t1 : FE := {rec(T1)}\ndef value : FE := {rec(O)}\n'
head+='''theorem quarter : (4:FE)⁻¹=536870912 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
'''
for name,expr in [('horner2','h2+alpha*h3=t2'),('horner1','h1+alpha*t2=t1'),('horner0','h0+alpha*t1=value')]:
 head+=f'''theorem {name} : {expr} := by
  unfold {dict(horner2='h2 alpha h3 t2',horner1='h1 alpha t2 t1',horner0='h0 alpha t1 value')[name]}
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
'''
head+='''#print axioms quarter
#print axioms horner2
#print axioms horner1
#print axioms horner0
end AspisR1.JFw_TX2_CircleNumbers
end
'''
emit('lean/JFw_TX2_CircleNumbers.lean',head)
