"""Bounded opening transcript SHA certificates, four compression blocks per file.
Each round is one named primitive transition. Python numbers are checked by Lean.
"""
from pathlib import Path
import re,json,hashlib,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
core=(R/'lean/JFp_SHA256.lean').read_text()
K=list(map(int,re.search(r'def constants : List Nat := \[(.*?)\]',core,re.S)[1].replace('\n','').split(',')))
IV=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225]
mask=2**32-1;ror=lambda x,n:((x>>n)|(x<<(32-n)))&mask
s0=lambda x:ror(x,7)^ror(x,18)^(x>>3);s1=lambda x:ror(x,17)^ror(x,19)^(x>>10)
b0=lambda x:ror(x,2)^ror(x,13)^ror(x,22);b1=lambda x:ror(x,6)^ror(x,11)^ror(x,25)
def step(s,k,w):
 a,b,c,d,e,f,g,h=s;t1=h+b1(e)+((e&f)^((e^mask)&g))+k+w;t2=b0(a)+((a&b)^(a&c)^(b&c))
 return [(t1+t2)&mask,a,b,c,(d+t1)&mask,e,f,g]
def advance(w):return w[1:]+[(s1(w[14])+w[9]+s0(w[1])+w[0])&mask]
ls=lambda xs:'['+','.join(map(str,xs))+']';reg=lambda xs:'⟨'+','.join(map(str,xs))+'⟩'
files={};order=[];msgs=json.loads((P/'JGe_OPENING_DIAGNOSTIC.json').read_text())['messages'];blocks_total=0
for label,raw in msgs.items():
 msg=bytes(raw); padded=msg+b'\x80'+bytes((55-len(msg))%64)+(8*len(msg)).to_bytes(8,'big')
 n=len(padded)//64;blocks_total+=n;name='JGe_'+label;ns='AspisR1.'+name;chunks=[];h=IV
 for start in range(0,n,4):
  mod=name+f'Blocks{start:02}';chunks.append(mod);order.append(mod)
  out=['import JFp_SHA256','set_option autoImplicit false',f'namespace {ns}','open JFp_SHA256']
  for block in range(start,min(start+4,n)):
   b=padded[64*block:64*(block+1)];w=[int.from_bytes(b[j:j+4],'big') for j in range(0,64,4)];s=h
   out += [f'namespace B{block:02}',f'def input : List Nat := {ls(b)}',f'def start : Reg := {reg(h)}',f'def w00 : List Nat := {ls(w)}','def s00 : Reg := start','theorem parsed : words input=w00 := by rfl','#print axioms parsed']
   for j,k in enumerate(K):
    sn=step(s,k,w[0]);wn=advance(w)
    out += [f'def w{j+1:02} : List Nat := {ls(wn)}',f'def s{j+1:02} : Reg := {reg(sn)}',f'theorem word{j:02} : advance w{j:02}=w{j+1:02} := by rfl',f'theorem round{j:02} : round s{j:02} {k} (w{j:02}.getD 0 0)=s{j+1:02} := by rfl',f'#print axioms word{j:02}',f'#print axioms round{j:02}'];s,w=sn,wn
   hn=[(x+y)&mask for x,y in zip(h,s)]
   out += [f'def result : Reg := {reg(hn)}','theorem checked : compress start (words input)=result := by','  rw [parsed]','  unfold compress loop','  change add start (constants.foldl transition (w00,s00)).2=result','  unfold constants']
   for j in range(64):out += [f'  rw [List.foldl_cons,transition,word{j:02},round{j:02}]']
   out += ['  rw [List.foldl_nil]','  rfl','#print axioms checked',f'end B{block:02}'];h=hn
  out += [f'end {ns}'];files[R/'lean'/(mod+'.lean')]='\n'.join(out)+'\n'
 assert b''.join(x.to_bytes(4,'big') for x in h)==hashlib.sha256(msg).digest()
 out=[f'import {m}' for m in chunks]+['import JFp_SeedHash','set_option autoImplicit false',f'namespace {ns}','open JFp_SHA256 JFp_SeedHash',f'def message : List Nat := {ls(raw)}','def chunks : List (List Nat) := ['+','.join(f'B{i:02}.input' for i in range(n))+']']
 out += ['theorem padded : pad message=chunks.flatten := by rfl','#print axioms padded']
 for i in range(n):out += [f'theorem lenB{i:02} : B{i:02}.input.length=64 := by rfl',f'#print axioms lenB{i:02}']
 out += ['theorem lengths : ∀ c∈chunks,c.length=64 := by','  intro c hc','  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc','  rcases hc with '+' | '.join(f'h{i}' for i in range(n))]
 for i in range(n):out += [f'  · subst c;exact lenB{i:02}']
 out += ['#print axioms lengths',f'theorem paddedLength : (pad message).length={64*n} := by','  rw [padded]','  simp only [chunks,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,'+','.join(f'lenB{i:02}' for i in range(n))+']','#print axioms paddedLength','theorem blockList : blocks ((pad message).length/64) (pad message)=chunks := by','  rw [paddedLength,padded]','  exact blocks_chunks chunks lengths','#print axioms blockList',f'def result : Reg := B{n-1:02}.result','theorem checked : JFp_SHA256.hash message=result := by','  unfold JFp_SHA256.hash','  dsimp only','  rw [blockList]','  simp only [chunks,List.foldl_cons,List.foldl_nil]','  rw [show initial=B00.start from rfl,B00.checked]']
 for i in range(1,n):out += [f'  rw [show B{i-1:02}.result=B{i:02}.start from rfl,B{i:02}.checked]']
 out += ['  rfl','#print axioms checked',f'end {ns}'];files[R/'lean'/(name+'.lean')]='\n'.join(out)+'\n';order.append(name)
# Long messages retain a symbolic full-block prefix and a bounded tail.
# Never reduce pad through a thousand-element literal list.
for label,raw in msgs.items():
 if len(raw)<=256:continue
 name='JGe_'+label;p=R/'lean'/(name+'.lean');txt=files[p]
 nf=len(raw)//64;nt=len(raw)%64;n=(len(raw)+9+63)//64
 heads=','.join(f'B{i:02}.input' for i in range(nf))
 tails=','.join(f'B{i:02}.input' for i in range(nf,n))
 lens='\n'.join(f'theorem lenB{i:02} : B{i:02}.input.length=64 := by rfl\n#print axioms lenB{i:02}' for i in range(n))
 padding=(55-len(raw))%64;endbytes=list((8*len(raw)).to_bytes(8,'big'))
 new=lens+'\n'+f'def head : List (List Nat) := [{heads}]\ndef tail : List Nat := {ls(raw[64*nf:])}\ndef message : List Nat := head.flatten ++ tail\ndef chunks : List (List Nat) := head ++ [{tails}]\n'
 new+=f'theorem tailLength : tail.length={nt} := by rfl\n#print axioms tailLength\ntheorem headLength : head.flatten.length={64*nf} := by\n  simp only [head,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,'+','.join(f'lenB{i:02}' for i in range(nf))+']\n  omega\n#print axioms headLength\n'
 new+=f'theorem messageLength : message.length={len(raw)} := by\n  simp only [message,List.length_append,headLength,tailLength]\n#print axioms messageLength\n'
 new+=f'theorem tailPad : tail ++ [128] ++ List.replicate {padding} 0 ++ {ls(endbytes)}=[{tails}].flatten := by rfl\n#print axioms tailPad\ntheorem padded : pad message=chunks.flatten := by\n  rw [pad,messageLength]\n  change (head.flatten ++ tail) ++ [128] ++ List.replicate {padding} 0 ++ {ls(endbytes)}=_\n  simp only [List.append_assoc,chunks,List.flatten_append]\n  exact congrArg (fun t => head.flatten ++ t) (by simpa only [List.append_assoc] using tailPad)\n#print axioms padded\n'
 start=txt.index('def message : List Nat :=');end=txt.index('theorem lengths :')
 txt=txt[:start]+new+txt[end:]
 txt=txt.replace('chunks,List.mem_cons,','chunks,head,List.mem_append,List.mem_cons,').replace('List.not_mem_nil,or_false]','List.not_mem_nil,or_false,or_assoc]')
 txt=txt.replace('chunks,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,','chunks,head,List.flatten_append,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,')
 txt=txt.replace('chunks,List.foldl_cons,List.foldl_nil]','chunks,head,List.foldl_append,List.foldl_cons,List.foldl_nil]')
 files[p]=txt
# Keep the already checked Init block separate. Other final chunks include
# their own digest aggregation, avoiding a compile used solely for imports.
for label in msgs:
 if label=='Init':continue
 name='JGe_'+label
 chunkmods=[m for m in order if m.startswith(name+'Blocks')]
 last=chunkmods[-1]
 blocktext=files.pop(R/'lean'/(last+'.lean'))
 agg=files[R/'lean'/(name+'.lean')]
 agg=agg.replace('import '+last+'\n','')
 lines=agg.splitlines();i=next(i for i,l in enumerate(lines) if l.startswith('namespace '))
 merged='\n'.join(lines[:i])+ '\n'+ '\n'.join(blocktext.splitlines()[2:])+'\n'+'\n'.join(lines[i:])+'\n'
 files[R/'lean'/(name+'.lean')]=merged
 order.remove(last)
files[P/'JGe_SHA_MANIFEST.json']=json.dumps({'blocks':blocks_total,'module_order':order,'messages':{k:hashlib.sha256(bytes(v)).hexdigest() for k,v in msgs.items()}},indent=2)+'\n'
for p,s in files.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(order),'modules;',blocks_total,'blocks')
