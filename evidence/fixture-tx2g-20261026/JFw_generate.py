from pathlib import Path
import json,sys
def emit(path,text):
 p=Path(path)
 if "--check" in sys.argv:
  assert p.read_text()==text,str(p)
 else:p.write_text(text)

P=2147483647
G=[855639275,1483149559,1898717401,1849775942,1112406525,1796814865,1838939499,418714188]
def add(a,b):return [(x+y)%P for x,y in zip(a,b)]
def mul(a,b):
 if len(a)==1:return [a[0]*b[0]%P]
 n=len(a)//2
 lo=mul(a[:n],b[:n]); hi=mul(a[n:],b[n:])
 if n==1: rh=[-hi[0]%P]
 elif n==2: rh=mul(hi,[2,1])
 else: rh=mul(hi,[0,0,1,0])
 return add(lo,rh)+add(mul(a[:n],b[n:]),mul(a[n:],b[:n]))
def record(a,suffix=''):
 if len(a)==1:return str(a[0])+suffix
 n=len(a)//2
 return '⟨'+record(a[:n],suffix)+','+record(a[n:],suffix)+'⟩'
v=[[1,0,0,0,0,0,0,0]]
for k in range(28):v.append(mul(v[-1],G))
emit('evidence/fixture-tx2g-20261026/JFw_POWERS.json',json.dumps(v,indent=2)+'\n')
for k in range(29):
 mod=f'JFw_TX2_P{k:02}'
 imports='JFw_TX2_PowersExplicit' if k==0 else f'JFw_TX2_P{k-1:02}'
 s=f'''import {imports}
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := {record(v[k],'#u32')}
theorem canonical : FIo_WideValues.Canon value := by
  change (({v[k][0]}<2147483647 ∧ {v[k][1]}<2147483647) ∧ ({v[k][2]}<2147483647 ∧ {v[k][3]}<2147483647)) ∧
    (({v[k][4]}<2147483647 ∧ {v[k][5]}<2147483647) ∧ ({v[k][6]}<2147483647 ∧ {v[k][7]}<2147483647))
  omega
'''
 if k==0:
  s+='''theorem meaning : decode value=decode gamma^0 := by
  change (1 : AspisWideTower.WideExact)=_ ^ 0
  rw [pow_zero]
'''
 else:
  prev=f'JFw_TX2_P{k-1:02}'
  s+=f'''theorem step : decode {prev}.value * decode gamma=decode value := by
  change ({record(v[k-1])} : AspisWideTower.WideExact)*{record(G)}={record(v[k])}
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R]
theorem meaning : decode value=decode gamma^{k} := by
  rw [show {k}=({k-1}:Nat)+1 from rfl,pow_succ,← {prev}.meaning]
  exact step.symm
'''
 s+=f'''theorem source : entry {k}=value := identify {k} value canonical meaning
#print axioms canonical
'''
 if k:s+='#print axioms step\n'
 s+=f'''#print axioms meaning
#print axioms source
end AspisR1.{mod}
end
'''
 if k==2:s=s.replace('AspisV8R15.ExactTowerBase.qm31R]', 'AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P] <;> decide')
 if k>=3:
  def rawadd(x,y):return [a+b for a,b in zip(x,y)]
  def rawmul(x,y):
   if len(x)==1:return [x[0]*y[0]]
   n=len(x)//2;lo=rawmul(x[:n],y[:n]);hi=rawmul(x[n:],y[n:]);rh=([-hi[0]] if n==1 else rawmul(hi,[2,1] if n==2 else [0,0,1,0]))
   return rawadd(lo,rh)+rawadd(rawmul(x[:n],y[n:]),rawmul(x[n:],y[:n]))
  lanes=''.join(f'theorem lane{j} : ({x} : ZMod 2147483647)={v[k][j]} := by decide\n' for j,x in enumerate(rawmul(v[k-1],G)))
  s=s.replace('theorem step :',lanes+'theorem step :')
  s=s.replace('AspisV8R15.ExactTowerBase.qm31R]\n','AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]\n'+''.join(f'  · exact lane{j}\n' for j in range(8)))
  s=s.replace('#print axioms step',''.join(f'#print axioms lane{j}\n' for j in range(8))+'#print axioms step')
 emit('lean/'+mod+'.lean',s)
