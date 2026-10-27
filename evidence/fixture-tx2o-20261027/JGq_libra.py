from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
P=2147483647;perm=[0,3,2,1]
def q(v):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(v)
alpha=x['nums']('JGo_TX2_WeightData','alpha');aps=[]
for tag in [0,1]:
 a=x['scalar']('JFq_Alpha'+str(tag));v=[[1]+[0]*7]
 for _ in range(3):v.append(x['mul'](v[-1],a))
 aps.append(v)
out={};data='''import JGq_Powers0
import JGq_Powers1
import JGo_TX2_WeightData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Libra
open Aeneas Aeneas.Std Result
'''
allp=[]
for side in range(2):
 qq=alpha[32+4*side:36+4*side];powers=[[1,0,0,0],qq]
 for i in range(2,21):powers.append(x['qmul'](powers[-1],qq))
 allp.append(powers)
 for i in [0,1,2,3,4,8,12,16,20]:data+=f'def q{side}_{i} : FIo_Install.NQ := '+q(powers[i])+'\n'
 data+=f'def row{side} : Array FIo_Install.NQ 4#usize := Array.make 4#usize [q{side}_0,q{side}_1,q{side}_2,q{side}_3]\n'
 terms=[]
 for j in range(4):
  m=x['mul'](aps[1][perm[j]],powers[4*j]+[0]*4);t=[(a*pow(4,-1,P))%P for a in m];terms.append(t)
  data+=f'def product{side}_{j} : FIo_Install.NE := '+x['wide'](m)+'\n'+f'def term{side}_{j} : FIo_Install.NE := '+x['wide'](t)+'\n'
 for n in [2,3,4]:
  v=[sum(t[i] for t in terms[:n])%P for i in range(8)]
  data+=f'def sum{side}_{n} : FIo_Install.NE := '+x['wide'](v)+'\n'
 data+=f'''theorem extra{side} : Array.index_usize (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {side}#usize=ok q{side}_1 := by rfl
#print axioms extra{side}
'''
out['JGq_LibraData']=data+'end AspisR1.JGq_Libra\nend\n'
for side in range(2):
 s='''import JGq_LibraData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Libra
open Aeneas Aeneas.Std Result
'''
 calls=[(f'FIo_Native.aspis_core.field.QM31.mul FIo_Native.aspis_core.field.QM31.ONE q{side}_1',1),
 (f'FIo_Native.aspis_core.field.QM31.mul q{side}_1 q{side}_1',2),
 (f'FIo_Native.aspis_core.field.QM31.mul q{side}_2 q{side}_1',3),
 (f'FIo_Native.aspis_core.field.QM31.mul q{side}_3 q{side}_1',4),
 (f'FIo_Native.aspis_core.field.QM31.square q{side}_2',4),
 (f'FIo_Native.aspis_core.field.QM31.square q{side}_4',8),
 (f'FIo_Native.aspis_core.field.QM31.mul q{side}_8 q{side}_4',12),
 (f'FIo_Native.aspis_core.field.QM31.square q{side}_8',16),
 (f'FIo_Native.aspis_core.field.QM31.mul q{side}_16 q{side}_4',20)]
 for i,(call,v) in enumerate(calls):s+=f'theorem power{side}_{i} : {call}=ok q{side}_{v} := by with_unfolding_all rfl\n#print axioms power{side}_{i}\n'
 out[f'JGq_LibraPowers{side}']=s+'end AspisR1.JGq_Libra\nend\n'
 s='''import JGq_LibraData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Libra
open Aeneas Aeneas.Std Result
'''
 for j in range(4):
  s+=f'''theorem mixed{side}_{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 JGq_Powers1.p{perm[j]} q{side}_{4*j}=ok product{side}_{j} := by with_unfolding_all rfl
#print axioms mixed{side}_{j}
theorem quarter{side}_{j} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product{side}_{j} FIo_Native.weights.QUARTER=ok term{side}_{j} := by with_unfolding_all rfl
#print axioms quarter{side}_{j}
'''
 for n in [2,3,4]:
  left=f'term{side}_0' if n==2 else f'sum{side}_{n-1}'
  s+=f'theorem sum{side}call{n} : FIo_Native.aspis_core.field.wide_exact.WideExact.add {left} term{side}_{n-1}=ok sum{side}_{n} := by with_unfolding_all rfl\n#print axioms sum{side}call{n}\n'
 out[f'JGq_LibraTerms{side}']=s+'end AspisR1.JGq_Libra\nend\n'
 # Reuse the checked scalar-control method; specialize only numeric data and row.
 s=(R/'lean/JGq_Scale0.lean').read_text().replace('JGq_Scale0',f'JGq_LibraScale{side}')
 s=s.replace('import JGo_TX2_WeightData','import JGq_LibraData')
 s=re.sub(r'def row :[^\n]+',f'def row : Array FIo_Install.NQ 4#usize := JGq_Libra.row{side}',s)
 vs=[[0]*8]
 for j in range(4):vs.append(x['add'](vs[-1],x['mul'](aps[0][perm[j]],allp[side][j]+[0]*4)))
 for j,v in enumerate(vs):s=re.sub(rf'def v{j} :[^\n]+',f'def v{j} : E := '+x['wide'](v),s)
 s=re.sub(r'def value :[^\n]+','def value : E := '+x['wide']([(a*pow(4,-1,P))%P for a in vs[4]]),s)
 out[f'JGq_LibraScale{side}']=s
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'Libra primitive and scalar-call stages; no parent Libra success claimed')
