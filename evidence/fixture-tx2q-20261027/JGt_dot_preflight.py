"""Arithmetic diagnostic only; no Lean success or SHA256 realization claim."""
from pathlib import Path
import re,json,sys,hashlib
R=Path(__file__).resolve().parents[2]
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')}
exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
P=x['P'];qmul=x['qmul'];add=x['add'];mul=x['mul']
def ns_text(ns):
 for p in (R/'lean').glob(ns[:3]+'*.lean'):
  t=p.read_text();marker='namespace AspisR1.'+ns+'\n'
  if marker in t:return t.split(marker)[1].split('end AspisR1.')[0]
 raise ValueError(ns)
def definition(ns,name):
 t=ns_text(ns);return re.search(rf'def {name}[^\n]*:= (.*)',t).group(1)
def words(ns):
 d=definition(ns,'bytes');bs=bytes(map(int,re.findall(r'(\d+)#u8',d)))
 return [int.from_bytes(bs[i:i+4],'little') for i in range(0,len(bs),4)]
def basis(node):
 b=[1]
 for _ in range(6):b += [i*node%P for i in b];node=(2*node*node-1)%P
 return b
rhs=words('JFq_Rhs');power=words('JFq_Power');rho=words('JFq_Rho');weights=[words(f'JFq_Weight{i:02}') for i in range(64)]
states=[dict(rhs=rhs,power=power)];nodes=[];lines=[];bases=[]
for i in range(12):
 d=definition(f'JFz_TX2_Q{i}_Line','value');line=list(map(int,re.findall(r'(\d+)#u32',d)));assert len(line)==8
 node=int(re.search(rf'def value{i} : U32 := (\d+)#u32',ns_text('JFz_TX2_Nodes')).group(1));bs=basis(node)
 rhs=add(rhs,mul(line,power+[0]*4))
 weights=[add(w,[p*b%P for p in power]) for w,b in zip(weights,bs)]
 power=qmul(power,rho)
 states.append(dict(rhs=rhs,power=power));nodes.append(node);lines.append(line);bases.append(bs)
fields=[x['nums'](f'JGo_TX2_Message{i//8*8:02}',f'value{i:02}') for i in range(64)]
dot=[0]*8
for f,w in zip(fields,weights):dot=add(dot,mul(f,w+[0]*4))
result=dict(scope='Python arithmetic diagnostic only, no kernel gate proof',states=states,nodes=nodes,lines=lines,bases=bases,weights=weights,fields=fields,dot=dot,rhs=rhs,dot_equals_rhs=dot==rhs)
p=Path(__file__).with_name('JGt_DOT_PREFLIGHT.json');s=json.dumps(result,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('Dot diagnostic equals same query rhs:',result['dot_equals_rhs'])
