from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
M=2147483647
def add(x,y):return tuple((a+b)%M for a,b in zip(x,y))
def mul(x,y):
 def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%M,(a[0]*b[1]+a[1]*b[0])%M)
 p=cm(x[:2],y[:2]);q=cm(x[2:],y[2:]);r=cm(q,(2,1));s=cm(x[:2],y[2:]);t=cm(x[2:],y[:2])
 return ((p[0]+r[0])%M,(p[1]+r[1])%M,(s[0]+t[0])%M,(s[1]+t[1])%M)
def pow5(x):s=mul(x,x);return mul(mul(s,s),x)
def external(x):
 z=[]
 for i in range(4):
  a,b,c,d=x[4*i:4*i+4];ab=add(a,b);cd=add(c,d);t=add(ab,cd);u=add(t,b);v=add(t,d)
  z.extend([add(u,ab),add(u,add(c,c)),add(v,cd),add(v,add(a,a))])
 sums=[tuple(sum(z[4*g+c][k] for g in range(4))%M for k in range(4)) for c in range(4)]
 return [add(v,sums[i%4]) for i,v in enumerate(z)]
s=(R/'lean/JGl_NumericCanonical.lean').read_text()
def cells(name):
 body=s.split('theorem '+name+' :')[1].split('#print axioms')[0]
 return [tuple(map(int,re.findall(r'(\d+)<2147483647',l))) for l in body.splitlines() if 'change (' in l]
a=cells('a');low=cells('low')
c=(R/'docs/research/v8-r0-sem-proof-20261008/lean/R0P/PoseidonConstants.lean').read_text()
def constants(name):
 body=c.split('def '+name+' :')[1].split('/--')[0];v=[int(x,16) for x in re.findall('0x[0-9a-f]+',body)]
 return [v[i:i+16] for i in range(0,64,16)]
i=constants('poseidonExternalInitial');f=constants('poseidonExternalFinal')
def weight(rows):return [tuple(sum(low[t][k]*rows[n][j] for n,t in enumerate([1,9,10]))%M for k in range(4)) for j in range(16)]
even=weight([i[2],f[0],f[2]]);odd=weight([i[3],f[1],f[3]])
p0=[pow5(add(x,y)) for x,y in zip(a,even)];mid=external(p0);p1=[pow5(add(x,y)) for x,y in zip(mid,odd)];full=external(p1)
assert full==[tuple(v) for v in json.loads((R/'evidence/joint-fixture21-20261027/JGl_DIAGNOSTIC_VECTORS.json').read_text())['full']]
data=dict(even=even,odd=odd,powered0=p0,mid=mid,powered1=p1)
def lit(w):return f'⟨⟨{w[0]}#u32,{w[1]}#u32⟩,⟨{w[2]}#u32,{w[3]}#u32⟩⟩'
files={}
files['JGn_FullPhaseData']='import JGl_VectorData\nset_option autoImplicit false\nnamespace AspisR1.JGn_FullPhaseData\nopen Aeneas Aeneas.Std FIq_Native\n'+''.join('def '+n+' : Array field.QM31 16#usize := ⟨['+','.join(map(lit,v))+'],by rfl⟩\n' for n,v in data.items())+'end AspisR1.JGn_FullPhaseData\n'
phases=[('Even','FJe_FullConstants.even JGl_NumericData.low','JGn_FullPhaseData.even'),('Odd','FJe_FullConstants.odd JGl_NumericData.low','JGn_FullPhaseData.odd'),('Pow0','(fun j : Fin 16=>R0P.poseidonPow5 (decoded JGl_NumericData.a j+decoded JGn_FullPhaseData.even j))','JGn_FullPhaseData.powered0'),('Mid','R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered0)','JGn_FullPhaseData.mid'),('Pow1','(fun j : Fin 16=>R0P.poseidonPow5 (decoded JGn_FullPhaseData.mid j+decoded JGn_FullPhaseData.odd j))','JGn_FullPhaseData.powered1'),('Final','R0P.poseidonExternalLinear (decoded JGn_FullPhaseData.powered1)','JGl_VectorData.full')]
for n,l,r in phases:
 mod='JGn_Full'+n
 t='import JGn_FullPhaseData\nimport JGl_WordProof\nimport FJe_FullConstants\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+mod+'\nopen FIw_ArrayValue (decoded)\n'
 for k in range(16):t+=f'theorem lane{k} : {l} ⟨{k},by decide⟩=decoded {r} ⟨{k},by decide⟩ := by\n  jgl_words\n#print axioms lane{k}\n'
 t+=f'theorem value : {l}=decoded {r} := by\n  funext i\n  fin_cases i\n'+''.join(f'  · exact lane{k}\n' for k in range(16))+'#print axioms value\nend AspisR1.'+mod+'\nend\n'
 files[mod]=t
for name,body in files.items():
 file=R/'lean'/(name+'.lean')
 if '--check' in sys.argv:assert file.read_text()==body,name
 else:file.write_text(body)
print('full certificate generator validated' if '--check' in sys.argv else 'full certificate generated; no large recurrence reduction emitted')
