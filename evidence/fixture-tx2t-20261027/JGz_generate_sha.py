"""Bounded SHA round certificates on retained native bytes. --check is byte exact.
No full-buffer reduction or successful hash leaf is emitted.
"""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
K=list(map(int,re.search(r'def constants : List Nat := \[(.*?)\]',(R/'lean/JFp_SHA256.lean').read_text(),re.S)[1].replace('\n','').split(',')))
IV=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225];mask=2**32-1
ror=lambda x,n:((x>>n)|(x<<(32-n)))&mask
s0=lambda x:ror(x,7)^ror(x,18)^(x>>3)
s1=lambda x:ror(x,17)^ror(x,19)^(x>>10)
b0=lambda x:ror(x,2)^ror(x,13)^ror(x,22)
b1=lambda x:ror(x,6)^ror(x,11)^ror(x,25)
def step(s,k,w):
 a,b,c,d,e,f,g,h=s;t1=h+b1(e)+((e&f)^((e^mask)&g))+k+w;t2=b0(a)+((a&b)^(a&c)^(b&c));return [(t1+t2)&mask,a,b,c,(d+t1)&mask,e,f,g]
def advance(w):return w[1:]+[(s1(w[14])+w[9]+s0(w[1])+w[0])&mask]
ls=lambda xs:'['+','.join(map(str,xs))+']'
reg=lambda xs:'⟨'+','.join(map(str,xs))+'⟩'
def retained(kind):
 b=bytearray()
 for f in sorted((R/'lean').glob(f'JFx_Data{kind}[0-9][0-9].lean')):
  for line in f.read_text().splitlines():
   if re.match(r'def c\d+ :',line):
    term=line.split(':=',1)[1]
    if 'List.replicate' in term:
     n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',term).groups());b.extend([v]*n)
    else:b.extend(map(int,re.findall(r'(\d+)#u8',term)))
 return bytes(b)
messages={'P':retained('Proof'),'U':retained('Public'),'C':b'UNPROVED:R1:checkpoint'+retained('Checkpoint')[:1736]}
# checksumParts is a literal 22-byte domain (the spelling is pinned below).
messages['C']=bytes([85,78,80,82,79,86,69,68,58,82,49,58,99,104,101,99,107,112,111,105,110,116])+retained('Checkpoint')[:1736]
files={};manifest={}
for kind,msg in messages.items():
 padded=msg+b'\x80'+bytes((55-len(msg))%64)+(8*len(msg)).to_bytes(8,'big');h=IV;mods=[]
 for group in range((len(padded)//64+15)//16):
  name=f'JGz_SHA{kind}{group:02}';mods.append(name)
  out=['import JFp_SHA256','set_option autoImplicit false',f'namespace AspisR1.{name}','open JFp_SHA256']
  block_names=[]
  for bi in range(16*group,min(16*(group+1),len(padded)//64)):
   bn=f'B{bi:03}';block_names.append(bn+'.input');out += [f'namespace {bn}']
   b=padded[64*bi:64*(bi+1)];w=[int.from_bytes(b[j:j+4],'big') for j in range(0,64,4)];s=h
   out += [f'def input : List Nat := {ls(b)}',f'def start : Reg := {reg(h)}',f'def w00 : List Nat := {ls(w)}',f'def s00 : Reg := start']
   for j,k in enumerate(K):
    sn=step(s,k,w[0]);wn=advance(w)
    out += [f'def w{j+1:02} : List Nat := {ls(wn)}',f'def s{j+1:02} : Reg := {reg(sn)}'];s,w=sn,wn
   hn=[(x+y)&mask for x,y in zip(h,s)]
   out += [f'def result : Reg := {reg(hn)}','theorem checked : compress start (words input)=result := by','  have parsed : words input=w00 := by rfl','  rw [parsed]','  unfold compress loop','  change add start (constants.foldl transition (w00,s00)).2=result']
   for j,k in enumerate(K):out += [f'  have t{j:02} : transition (w{j:02},s{j:02}) {k}=(w{j+1:02},s{j+1:02}) := by rfl']
   out += ['  unfold constants']
   for j in range(64):out += [f'  rw [List.foldl_cons,t{j:02}]']
   out += ['  rw [List.foldl_nil]','  rfl','#print axioms checked',f'end {bn}'];h=hn
  out += ['def chunks : List (List Nat) := ['+','.join(block_names)+']']
  if not (kind=='C' and group==0):
   first=16*group;last=min(16*(group+1),len(padded)//64)-1
   out += [f'theorem folded : chunks.foldl (fun s b=>compress s (words b)) B{first:03}.start=B{last:03}.result := by', '  unfold chunks','  simp only [List.foldl_cons,List.foldl_nil]']
   for bi in range(first,last+1):
    if bi>first:out += [f'  rw [show B{bi-1:03}.result=B{bi:03}.start from rfl]']
    out += [f'  rw [B{bi:03}.checked]']
   out += ['#print axioms folded', 'theorem lengths : ∀ b ∈ chunks,b.length=64 := by','  intro b hb','  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hb', '  rcases hb with '+'|'.join('h'+str(bi) for bi in range(first,last+1))]
   for bi in range(first,last+1):out += [f'  · subst b;rfl']
   out += ['#print axioms lengths']
  out += [f'end AspisR1.{name}']
  files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n'
 digest=bytes.fromhex(''.join(f'{x:08x}' for x in h));assert digest==hashlib.sha256(msg).digest()
 manifest[kind]=dict(bytes=len(msg),blocks=len(padded)//64,sha256=digest.hex(),modules=mods)
files[P/'JGz_SHA_MANIFEST.json']=json.dumps(manifest,indent=2)+'\n'
for path,source in files.items():
 if '--check' in sys.argv:assert path.read_text()==source,path
 else:path.write_text(source)
print(('checked' if '--check' in sys.argv else 'generated'),len(files),'files',json.dumps({k:(v['blocks'],v['sha256']) for k,v in manifest.items()}))
