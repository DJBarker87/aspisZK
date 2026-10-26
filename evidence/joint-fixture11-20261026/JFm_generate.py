"""Generate bounded SHA windows and native row calls; check reproduces all files.
No whole hash recurrence is normalized: compression words/rounds are named leaves.
"""
from pathlib import Path
import re,json,hashlib,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
K=list(map(int,re.search(r'def constants : List Nat := \[(.*?)\]',(R/'lean/JFp_SHA256.lean').read_text(),re.S)[1].replace('\n','').split(',')))
IV=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225];mask=2**32-1
ror=lambda x,n:((x>>n)|(x<<(32-n)))&mask
s0=lambda x:ror(x,7)^ror(x,18)^(x>>3);s1=lambda x:ror(x,17)^ror(x,19)^(x>>10)
b0=lambda x:ror(x,2)^ror(x,13)^ror(x,22);b1=lambda x:ror(x,6)^ror(x,11)^ror(x,25)
def step(s,k,w):
 a,b,c,d,e,f,g,h=s;t1=h+b1(e)+((e&f)^((e^mask)&g))+k+w;t2=b0(a)+((a&b)^(a&c)^(b&c))
 return [(t1+t2)&mask,a,b,c,(d+t1)&mask,e,f,g]
def advance(w):return w[1:]+[(s1(w[14])+w[9]+s0(w[1])+w[0])&mask]
ls=lambda xs:'['+','.join(map(str,xs))+']';reg=lambda xs:'⟨'+','.join(map(str,xs))+'⟩'
files={};pins=[]
def cert(name,msg):
 padded=msg+b'\x80'+bytes((55-len(msg))%64)+(8*len(msg)).to_bytes(8,'big');out=['import JFp_SHABlocks','set_option autoImplicit false',f'namespace AspisR1.{name}','open JFp_SHA256',f'def message : List Nat := {ls(msg)}'];h=IV;ns=[]
 for bi,off in enumerate(range(0,len(padded),64)):
  bn=f'B{bi:02}';ns.append(bn);chunk=padded[off:off+64];w=[int.from_bytes(chunk[j:j+4],'big') for j in range(0,64,4)];s=h
  out += [f'namespace {bn}',f'def input : List Nat := {ls(chunk)}',f'def start : Reg := {reg(h)}',f'def w00 : List Nat := {ls(w)}',f'def s00 : Reg := start','theorem parsed : words input=w00 := by rfl','#print axioms parsed']
  for j,k in enumerate(K):
   sn=step(s,k,w[0]);wn=advance(w)
   out += [f'def w{j+1:02} : List Nat := {ls(wn)}',f'def s{j+1:02} : Reg := {reg(sn)}',f'theorem word{j:02} : advance w{j:02}=w{j+1:02} := by rfl',f'theorem round{j:02} : round s{j:02} {k} (w{j:02}.getD 0 0)=s{j+1:02} := by rfl',f'#print axioms word{j:02}',f'#print axioms round{j:02}'];s,w=sn,wn
  h=[(x+y)&mask for x,y in zip(h,s)]
  out += [f'def result : Reg := {reg(h)}','theorem checked : compress start (words input)=result := by','  rw [parsed]','  unfold compress loop','  change add start (constants.foldl transition (w00,s00)).2=result','  unfold constants']
  out += [f'  rw [List.foldl_cons,transition,word{j:02},round{j:02}]' for j in range(64)]
  out += ['  rw [List.foldl_nil]','  rfl','#print axioms checked',f'end {bn}']
 out += ['def chunks : List (List Nat) := ['+','.join(n+'.input' for n in ns)+']','theorem padded : pad message=chunks.flatten := by rfl','#print axioms padded','theorem lengths : ∀ c ∈ chunks,c.length=64 := by','  intro c hc','  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc','  rcases hc with '+'|'.join('h'+str(i) for i in range(len(ns)))]
 out += [f'  · subst c; rfl' for _ in ns]
 out += ['#print axioms lengths',f'theorem paddedLength : (pad message).length={len(padded)} := by rfl','#print axioms paddedLength','theorem blockList : blocks ((pad message).length/64) (pad message)=chunks := by','  rw [paddedLength,padded]','  exact blocks_chunks chunks lengths','#print axioms blockList',f'def result : Reg := {ns[-1]}.result','theorem checked : JFp_SHA256.hash message=result := by','  unfold JFp_SHA256.hash','  dsimp only','  rw [blockList]','  simp only [chunks,List.foldl_cons,List.foldl_nil]','  rw [show initial=B00.start from rfl,B00.checked]']
 for prev,nxt in zip(ns,ns[1:]):out += [f'  rw [show {prev}.result={nxt}.start from rfl,{nxt}.checked]']
 out += ['  rfl','#print axioms checked',f'end AspisR1.{name}'];files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n'
 digest=b''.join(x.to_bytes(4,'big') for x in h);assert digest==hashlib.sha256(msg).digest();return digest
raw=[]
for f in sorted((R/'lean').glob('JFx_DataProof*.lean')):
 for line in f.read_text().splitlines():
  if line.startswith('def c'):
   if 'replicate' in line:
    n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',line).groups());raw += [v]*n
   else:raw += list(map(int,re.findall(r'(\d+)#u8',line)))
assert len(raw)==57607
state=bytes.fromhex(json.loads((R/'evidence/joint-fixture10-20261026/JFp_SHA_INPUT.json').read_text())['seed'])
for row in range(27):
 text=(R/f'lean/JFw_NativeRow{row:02}.lean').read_text();head=list(map(int,re.search(r'def record.*?frame (\d+)#u8 (\d+)#u8 (\d+)#u8 (\d+)#u8 (\d+)#u8',text)[0].split('frame ')[1].replace('#u8','').split()))
 if m:=re.search(r'def payload.*?expandedPayload (\d+) (\d+)',text):
  n,off=map(int,m.groups());payload=sum([raw[off+16*j:off+16*j+16]+[0]*16 for j in range(n)],[])
 else:
  off,n=map(int,re.search(r'def payload.*?window (\d+) (\d+)',text).groups());payload=raw[off:off+n]
 frame=bytes(head+payload);a=state+bytes([0,160+row])+frame
 absorbed=hashlib.sha256(a).digest();read=hashlib.sha256(absorbed+b'\x01').digest();ratchet=hashlib.sha256(absorbed+b'\x02').digest()
 if row:
  cert(f'JFm_Q{row:02}Absorb',a);cert(f'JFm_Q{row:02}Read',absorbed+b'\x01');cert(f'JFm_Q{row:02}Ratchet',absorbed+b'\x02')
 pins.append(dict(row=row,frame=list(frame),before=list(state),absorbed=list(absorbed),read=list(read),after=list(ratchet),coordinates=[(int.from_bytes(read,'little')//(2147483647**i))%2147483647 for i in range(4)]));state=ratchet
for row in range(1,27):
 read=R/f'lean/JFm_Q{row:02}Read.lean';ratchet=R/f'lean/JFm_Q{row:02}Ratchet.lean'
 files[R/f'lean/JFm_Q{row:02}Reads.lean']=files.pop(read)+'\n'+files.pop(ratchet).replace('import JFp_SHABlocks\nset_option autoImplicit false\n','')
files[P/'JFm_WINDOWS.json']=json.dumps(pins,indent=2)+'\n'
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,str(f)
 else:f.write_text(s)
print(json.dumps(dict(files=len(files),check='--check' in sys.argv)))
