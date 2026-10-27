"""Bounded first-query certificates, derived from the retained proof window."""
from pathlib import Path
import re,json,hashlib,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
K=list(map(int,re.search(r'def constants : List Nat := \[(.*?)\]',(R/'lean/JFp_SHA256.lean').read_text(),re.S)[1].replace('\n','').split(',')))
IV=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225]
mask=2**32-1;ror=lambda x,n:((x>>n)|(x<<(32-n)))&mask
s0=lambda x:ror(x,7)^ror(x,18)^(x>>3);s1=lambda x:ror(x,17)^ror(x,19)^(x>>10)
b0=lambda x:ror(x,2)^ror(x,13)^ror(x,22);b1=lambda x:ror(x,6)^ror(x,11)^ror(x,25)
def step(s,k,w):
 a,b,c,d,e,f,g,h=s;t1=h+b1(e)+((e&f)^((e^mask)&g))+k+w;t2=b0(a)+((a&b)^(a&c)^(b&c))
 return [(t1+t2)&mask,a,b,c,(d+t1)&mask,e,f,g]
def advance(w):return w[1:]+[(s1(w[14])+w[9]+s0(w[1])+w[0])&mask]
ls=lambda xs:'['+','.join(map(str,xs))+']';reg=lambda xs:'⟨'+','.join(map(str,xs))+'⟩'
seed=bytes.fromhex(json.loads((P/'JFp_SHA_INPUT.json').read_text())['seed'])
# row0's actual selected compact header is empty-payload [0,0,0,0,0].
raw=[]
for line in (R/'lean/JFx_DataProof00.lean').read_text().splitlines():
 if line.startswith('def c'):
  if 'replicate' in line:
   n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',line).groups());raw += [v]*n
  else:raw += list(map(int,re.findall(r'(\d+)#u8',line)))
frame=bytes(raw[48:53]);assert frame==bytes(5)
absorb=seed+bytes([0,160])+frame;absorbed=hashlib.sha256(absorb).digest()
messages={'Absorb':absorb,'Read':absorbed+bytes([1]),'Ratchet':absorbed+bytes([2])};pins={}
for label,msg in messages.items():
 name='JFp_Query00'+label;ns='AspisR1.'+name
 padded=msg+b'\x80'+bytes((55-len(msg))%64)+(8*len(msg)).to_bytes(8,'big');assert len(padded)==64
 w=[int.from_bytes(padded[j:j+4],'big') for j in range(0,64,4)];s=IV
 out=['import JFp_SHA256','set_option autoImplicit false',f'namespace {ns}','open JFp_SHA256',f'def message : List Nat := {ls(list(msg))}',f'def input : List Nat := {ls(list(padded))}',f'def w00 : List Nat := {ls(w)}',f'def s00 : Reg := initial','theorem parsed : words input=w00 := by rfl','#print axioms parsed']
 for j,k in enumerate(K):
  sn=step(s,k,w[0]);wn=advance(w)
  out += [f'def w{j+1:02} : List Nat := {ls(wn)}',f'def s{j+1:02} : Reg := {reg(sn)}',f'theorem word{j:02} : advance w{j:02}=w{j+1:02} := by rfl',f'theorem round{j:02} : round s{j:02} {k} (w{j:02}.getD 0 0)=s{j+1:02} := by rfl',f'#print axioms word{j:02}',f'#print axioms round{j:02}'];s,w=sn,wn
 result=[(x+y)&mask for x,y in zip(IV,s)]
 out += [f'def result : Reg := {reg(result)}','theorem compression : compress initial (words input)=result := by','  rw [parsed]','  unfold compress loop','  change add initial (constants.foldl transition (w00,s00)).2=result','  unfold constants']
 for j in range(64):out += [f'  rw [List.foldl_cons,transition,word{j:02},round{j:02}]']
 out += ['  rw [List.foldl_nil]','  rfl','#print axioms compression','theorem padded : pad message=input := by rfl','#print axioms padded','theorem checked : JFp_SHA256.hash message=result := by','  unfold JFp_SHA256.hash','  dsimp only','  rw [padded]','  change compress initial (words input)=result','  exact compression','#print axioms checked',f'end {ns}']
 text='\n'.join(out)+'\n';f=R/'lean'/(name+'.lean')
 if '--check' in sys.argv:assert f.read_text()==text
 else:f.write_text(text)
 digest=b''.join(x.to_bytes(4,'big') for x in result);assert digest==hashlib.sha256(msg).digest();pins[label]=dict(message=list(msg),digest=list(digest))
f=P/'JFp_QUERY00_DIAGNOSTIC.json';text=json.dumps(pins,indent=2)+'\n'
if '--check' in sys.argv:assert f.read_text()==text
else:f.write_text(text)
