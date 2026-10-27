from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];P=2147483647
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
add=x['add'];mul=x['mul'];qmul=x['qmul'];nums=x['nums'];zero=[0]*8
scale=lambda a,s:[v*s%P for v in a]
def qp(q,n):
 z=[1,0,0,0]
 for _ in range(n):z=qmul(z,q)
 return z
vals=[nums(f'JGo_TX2_Message{i//8*8:02}',f'value{i:02}') for i in range(64)]
aps=[]
for tag in [0,1]:
 a=x['scalar'](f'JFq_Alpha{tag}');ap=[[1]+[0]*7]
 for _ in range(3):ap.append(mul(ap[-1],a))
 aps.append(ap)
perm=[0,3,2,1];quarter=pow(4,-1,P)
def sf(row,ap):
 z=zero
 for j in range(4):z=add(z,mul(ap[perm[j]],row[4*j:4*j+4]+[0]*4))
 return scale(z,quarter)
parts=[zero[:] for _ in range(7)]
for kind,k in [(2,1),(5,3),(6,4)]:
 row=[nums('JGo_TX2_WeightData',f'f{k}{d}') for d in range(5)];summ=zero
 for j in range(64):
  coeff=[1,0,0,0]
  for d in [2,3,4]:coeff=qmul(coeff,row[d][4*((j//(4**(d-2)))%4):4*((j//(4**(d-2)))%4)+4])
  summ=add(summ,mul(vals[j],coeff+[0]*4))
 parts[kind]=mul(mul(sf(row[0],aps[0]),sf(row[1],aps[1])),summ)
for slot,definition in [(1,'value0'),(3,'value2')]:parts[slot]=nums('JGq_HighData',definition)
t=(R/'lean/FIo_NativeFuns.lean').read_text()
groups=list(map(int,re.findall(r'(\d+)#u8',re.search(r'def _root_\.FIo_Native.weights.S2_INACTIVE_GROUPS.*?\n\s*Array.make.*?\[(.*?)\]',t,re.S).group(1))))
masks=list(map(int,re.findall(r'(\d+)#u16',re.search(r'def _root_\.FIo_Native.weights.S2_INACTIVE_MASKS.*?\n\s*Array.make.*?\[(.*?)\]',t,re.S).group(1))))
low=[]
for j in range(16):low.append(scale(mul(aps[0][perm[j%4]],aps[1][perm[j//4]]),quarter*quarter%P))
for g in range(12):
 coeff=zero;weight=zero
 for j in range(64):
  if groups[j]==g:coeff=add(coeff,vals[j])
 for b in range(16):
  if masks[g]&(1<<b):weight=add(weight,low[b])
 parts[0]=add(parts[0],mul(coeff,weight))
libra=[zero[:] for _ in range(4)];alpha=nums('JGo_TX2_WeightData','alpha')
for side in [0,1]:
 q=alpha[32+4*side:36+4*side];lowv=sf(sum([qp(q,j) for j in range(4)],[]),aps[0]);terms=[scale(mul(aps[1][perm[j]],qp(q,4*j)+[0]*4),quarter) for j in range(4)]
 first2=add(*terms[:2]);first3=add(first2,terms[2]);allv=add(first3,terms[3])
 if side==0:
  libra[0]=mul(lowv,allv);libra[1]=mul(mul(lowv,first3),qp(q,16)+[0]*4)
 else:
  libra[1]=add(libra[1],mul(lowv,scale(aps[1][perm[3]],quarter)))
  libra[2]=mul(mul(lowv,allv),qp(q,4)+[0]*4);libra[3]=mul(mul(lowv,first2),qp(q,20)+[0]*4)
for j in range(4):parts[4]=add(parts[4],mul(vals[j],libra[j]))
k=x['scalar']('JFq_Kappa');power=[1]+[0]*7;total=zero
for j in range(7):total=add(total,mul(power,parts[j]));power=mul(power,k)
expected=nums('JGo_TX2_Horner1_6','after')
record=dict(scope='Python diagnostic only, not a kernel proof or successful native Pair',parts=parts,libra=libra,pair_result=total,expected=expected,pair_equal=total==expected)
(R/'evidence/fixture-tx2p-20261027/JGs_PREFLIGHT.json').write_text(json.dumps(record,indent=2)+'\n')
print('Pair diagnostic matches retained Horner:',record['pair_equal'])
