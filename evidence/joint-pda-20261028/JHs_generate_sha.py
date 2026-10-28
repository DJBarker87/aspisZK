"""Generate bounded per-round certificates; --check verifies exact reproduction.
No exceptional/sparse recurrence cells: each declaration checks one SHA round.
"""
from pathlib import Path
import json,re,sys,hashlib
ROOT=Path(__file__).resolve().parents[2]
DATA=json.loads((Path(__file__).parent/'JHs_CALLS.json').read_text())
source=(ROOT/'lean/JFp_SHA256.lean').read_text()
K=list(map(int,re.findall(r'\d+',source.split('def constants : List Nat := [')[1].split(']')[0])))
INITIAL=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225]
MASK=2**32-1

def rot(x,n):return ((x>>n)|(x<<(32-n)))&MASK

def advance(w):return w[1:]+[((rot(w[14],17)^rot(w[14],19)^(w[14]>>10))+w[9]+(rot(w[1],7)^rot(w[1],18)^(w[1]>>3))+w[0])&MASK]

def step(s,k,w):
 a,b,c,d,e,f,g,h=s;t1=h+(rot(e,6)^rot(e,11)^rot(e,25))+((e&f)^((e^MASK)&g))+k+w
 t2=(rot(a,2)^rot(a,13)^rot(a,22))+((a&b)^(a&c)^(b&c))
 return [(t1+t2)&MASK,a,b,c,(d+t1)&MASK,e,f,g]

def reg(s):return '⟨'+','.join(map(str,s))+'⟩'

def block(name,b,start):
 out=f'namespace {name}\ndef input : List Nat := {b}\ndef start : Reg := {reg(start)}\n';w=[int.from_bytes(bytes(b[i:i+4]),'big') for i in range(0,64,4)];s=start[:]
 for i in range(65):
  out+=f'def w{i:02} : List Nat := {w}\ndef s{i:02} : Reg := '+('start' if i==0 else reg(s))+'\n'
  if i<64:s=step(s,K[i],w[0]);w=advance(w)
 result=[(a+b)&MASK for a,b in zip(start,s)];out+=f'def result : Reg := {reg(result)}\n'
 out+='theorem checked : compress start (words input)=result := by\n  have parsed : words input=w00 := by rfl\n  rw [parsed]\n  unfold compress loop\n  change add start (constants.foldl transition (w00,s00)).2=result\n'
 for i,k in enumerate(K):out+=f'  have t{i:02} : transition (w{i:02},s{i:02}) {k}=(w{i+1:02},s{i+1:02}) := by rfl\n'
 out+='  unfold constants\n'
 for i in range(64):out+=f'  rw [List.foldl_cons,t{i:02}]\n'
 out+='  rw [List.foldl_nil]\n  rfl\n#print axioms checked\nend '+name+'\n'
 return out,result

outputs={}
for call in DATA:
 name=call['name'];raw=call['raw'];n=len(raw);padded=raw+[128]+[0]*((119-n%64)%64)+list((8*n).to_bytes(8,'big'));bs=[padded[i:i+64] for i in range(0,len(padded),64)];state=INITIAL[:]
 out='import JGz_HashTools\nset_option autoImplicit false\nnamespace AspisR1.JHs_SHA'+name+'\nopen JFp_SHA256\n'
 for i,b in enumerate(bs):
  fragment,state=block(f'B{i:03}',b,state);out+=fragment
 assert b''.join(x.to_bytes(4,'big') for x in state).hex()==call['sha256']
 out+=f'def raw : List Nat := {raw}\ndef result : Reg := B{len(bs)-1:03}.result\n'
 chunks='['+','.join(f'B{i:03}.input' for i in range(len(bs)))+']'
 if n>128:
  out+=f'def tail : List Nat := {raw[128:]}\n'
  out+=f'theorem rawSplit : raw = B000.input ++ B001.input ++ tail := by\n  simp only [raw, B000.input, B001.input, tail, List.cons_append, List.nil_append]\n#print axioms rawSplit\n'
  out+=f'theorem rawLength : raw.length = {n} := by\n  rw [rawSplit, List.length_append, List.length_append]\n  rw [show B000.input.length = 64 from rfl, show B001.input.length = 64 from rfl]\n  rfl\n#print axioms rawLength\n'
 else:
  out+=f'theorem rawLength : raw.length = {n} := rfl\n#print axioms rawLength\n' 
 out+='theorem padded : pad raw = '+chunks+'.flatten := by\n  rw [pad,rawLength]\n'
 out+=f'  change raw ++ [128] ++ List.replicate {(119-n%64)%64} 0 ++ {list((8*n).to_bytes(8,"big"))} = _\n  rfl\n#print axioms padded\n'
 out+='theorem lengths : ∀ b ∈ '+chunks+', b.length = 64 := by\n  intro b hb\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb\n'
 out+='  rcases hb with '+' | '.join(f'h{i}' for i in range(len(bs)))+'\n'
 for i in range(len(bs)):out+='  · subst b; rfl\n'
 out+='#print axioms lengths\n'
 out+='theorem checked : JFp_SHA256.hash raw = result := by\n'
 out+='  rw [JGz_HashTools.hash_chunks raw '+chunks+' padded lengths]\n'
 out+='  simp only [List.foldl_cons, List.foldl_nil]\n  rw [show initial = B000.start from rfl, B000.checked]\n'
 for i in range(1,len(bs)):out+=f'  rw [show B{i-1:03}.result = B{i:03}.start from rfl, B{i:03}.checked]\n'
 out+='  rfl\n#print axioms checked\nend AspisR1.JHs_SHA'+name+'\n'
 outputs[ROOT/'lean'/('JHs_SHA'+name+'.lean')]=out
for path,value in outputs.items():
 if '--check' in sys.argv:
  assert path.read_text()==value,path
 else:path.write_text(value)
print(json.dumps({'check':'--check' in sys.argv,'modules':len(outputs),'blocks':sum((len(c['raw'])+9+63)//64 for c in DATA),'rounds_per_block':64}))
