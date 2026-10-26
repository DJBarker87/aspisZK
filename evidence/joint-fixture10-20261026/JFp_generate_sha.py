"""Generate bounded SHA256 word/round certificates; never unfold a full hash.
All computed states are checked by Lean primitive-round equations. --check is
byte-exact generator validation, not an independent acceptance claim.
"""
from pathlib import Path
import json,re,hashlib,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
core=(R/'lean/JFp_SHA256.lean').read_text()
K=list(map(int,re.search(r'def constants : List Nat := \[(.*?)\]',core,re.S)[1].replace('\n','').split(',')))
IV=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225]
mask=2**32-1
ror=lambda x,n:((x>>n)|(x<<(32-n)))&mask
s0=lambda x:ror(x,7)^ror(x,18)^(x>>3)
s1=lambda x:ror(x,17)^ror(x,19)^(x>>10)
b0=lambda x:ror(x,2)^ror(x,13)^ror(x,22)
b1=lambda x:ror(x,6)^ror(x,11)^ror(x,25)
def step(s,k,w):
 a,b,c,d,e,f,g,h=s;t1=h+b1(e)+((e&f)^((e^mask)&g))+k+w;t2=b0(a)+((a&b)^(a&c)^(b&c))
 return [(t1+t2)&mask,a,b,c,(d+t1)&mask,e,f,g]
def advance(w):return w[1:]+[(s1(w[14])+w[9]+s0(w[1])+w[0])&mask]
ls=lambda xs:'['+','.join(map(str,xs))+']'
reg=lambda xs:'⟨'+','.join(map(str,xs))+'⟩'
seed=json.loads((R/'evidence/joint-fixture6-20261026/JFu_SEED_DIAGNOSTIC.json').read_text())
pub=json.loads((R/'evidence/joint-fixture6-20261026/JFu_SERIALIZATION_DIAGNOSTIC.json').read_text())['semantic_bytes']
msg=bytes.fromhex(seed['domain_hex'])+bytes([0])+len(pub).to_bytes(4,'little')+bytes(pub)+bytes.fromhex(seed['root_hex'])
assert len(msg)==1530 and hashlib.sha256(msg).hexdigest()==seed['init_input_sha256']
padded=msg+b'\x80'+bytes((55-len(msg))%64)+(8*len(msg)).to_bytes(8,'big')
files={};h=IV;proof=[]
for block in range(len(padded)//64):
 name=f'JFp_SHABlock{block:02}';ns='AspisR1.'+name
 b=padded[64*block:64*(block+1)];w=[int.from_bytes(b[j:j+4],'big') for j in range(0,64,4)];s=h
 out=['import JFp_SHA256','set_option autoImplicit false',f'namespace {ns}','open JFp_SHA256',f'def input : List Nat := {ls(list(b))}',f'def start : Reg := {reg(h)}',f'def w00 : List Nat := {ls(w)}',f'def s00 : Reg := start', 'theorem parsed : words input=w00 := by rfl','#print axioms parsed']
 for j,k in enumerate(K):
  sn=step(s,k,w[0]);wn=advance(w)
  out += [f'def w{j+1:02} : List Nat := {ls(wn)}',f'def s{j+1:02} : Reg := {reg(sn)}',f'theorem word{j:02} : advance w{j:02}=w{j+1:02} := by rfl',f'theorem round{j:02} : round s{j:02} {k} (w{j:02}.getD 0 0)=s{j+1:02} := by rfl',f'#print axioms word{j:02}',f'#print axioms round{j:02}']
  s,w=sn,wn
 hn=[(x+y)&mask for x,y in zip(h,s)]
 out += [f'def result : Reg := {reg(hn)}','theorem checked : compress start (words input)=result := by','  rw [parsed]','  unfold compress','  unfold loop','  change add start (constants.foldl transition (w00,s00)).2=result','  unfold constants']
 for j in range(64):out += [f'  rw [List.foldl_cons,transition,word{j:02},round{j:02}]']
 out += ['  rw [List.foldl_nil]','  rfl','#print axioms checked',f'end {ns}']
 files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n';h=hn
assert bytes.fromhex(''.join(f'{x:08x}' for x in h))==hashlib.sha256(msg).digest()
files[P/'JFp_SHA_INPUT.json']=json.dumps(dict(kind='generator input diagnostic; certificates check all SHA256 steps',message=list(msg),padded=list(padded),seed=seed['init_input_sha256'],blocks=25),indent=2)+'\n'
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(files),'files')
