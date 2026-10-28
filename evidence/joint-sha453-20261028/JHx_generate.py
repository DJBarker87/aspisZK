#!/usr/bin/env python3
"""Deterministic SHA round certificates; Python is a preflight, never a Lean axiom."""
from pathlib import Path
import re,json,hashlib,argparse,collections
E=Path(__file__).resolve().parent; R=E.parents[1]; L=R/'lean'
K=[int(x) for x in re.search(r'def constants : List Nat := \[(.*?)\]',(L/'JFp_SHA256.lean').read_text(),re.S)[1].replace('\n','').split(',')]
IV=[1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225]; MASK=2**32-1
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ro(x,n):return ((x>>n)|(x<<(32-n)))&MASK
def advance(w):return w[1:]+[((ro(w[14],17)^ro(w[14],19)^(w[14]>>10))+w[9]+(ro(w[1],7)^ro(w[1],18)^(w[1]>>3))+w[0])&MASK]
def rnd(s,k,w):
 a,b,c,d,e,f,g,h=s;t=h+(ro(e,6)^ro(e,11)^ro(e,25))+((e&f)^((e^MASK)&g))+k+w
 return [(t+(ro(a,2)^ro(a,13)^ro(a,22))+((a&b)^(a&c)^(b&c)))&MASK,a,b,c,(d+t)&MASK,e,f,g]
def traces(b,s):
 ws=[[int.from_bytes(bytes(b[j:j+4]),'big') for j in range(0,64,4)]];ss=[s]
 for k in K:ss.append(rnd(ss[-1],k,ws[-1][0]));ws.append(advance(ws[-1]))
 return ws,ss,[(a+b)&MASK for a,b in zip(s,ss[-1])]
def scan(text):
 scope=[];defs={}
 for line in text.splitlines():
  if line.startswith('namespace '):scope.append(line[10:])
  elif line.startswith('end ') and scope:scope.pop()
  elif m:=re.match(r'def (\w+) : (?:List \(List Nat\)|List Nat|Reg|State|Bytes) := (.*)',line):defs['.'.join(scope+[m[1]])]=(m[2],'.'.join(scope))
 return defs
D={};pins={}
for p in sorted(L.glob('*.lean')):
 if p.name.startswith(('JHe_SHAEquations','JGf_TX2_M0','JGh_TX2_M1','JGc_TX2_M2')):
  D.update(scan(p.read_text()));pins[p.name]=sha(p)
def reg(name):
 x,scope=D[name]
 if x.startswith('⟨'):return list(map(int,x.strip('⟨⟩').split(',')))
 return reg(scope+'.'+x)
def expected(expr):
 if expr.startswith('JFp_SHADigest.output '):return reg('AspisR1.'+expr.split()[-1])
 x,scope=D['AspisR1.'+expr];return expected(x)
def lit(xs):return '['+','.join(map(str,xs))+']'
def rl(xs):return '⟨'+','.join(map(str,xs))+'⟩'
def collect():
 out=[]
 for t,n in enumerate([157,157,139]):
  text=(L/f'JHe_SHAEquations{t}.lean').read_text()
  family=text.split(f'namespace JHe_SHAInputs{t}\n')[1]
  ins,exps=family.split('def expected')
  im=re.findall(r'\| (\d+|_) => (.*)',ins)
  em=re.findall(r'\| (\d+|_) => (.*)',exps)
  assert len(im)==len(em)==n
  for i,((ix,input_expr),(jx,expr)) in enumerate(zip(im,em)):
   if not input_expr.startswith('JGc_TX2_HashBytes.bytes '):input_expr=D['AspisR1.'+input_expr][0]
   ns=re.fullmatch(r'JGc_TX2_HashBytes.bytes (\S+)\.message',input_expr)[1]
   assert ix==jx and ix in (str(i),'_')
   full='AspisR1.'+ns; blocks=[]
   for j in range(100):
    bn=full+f'.B{j:02}'
    if bn+'.input' not in D:break
    b=json.loads(D[bn+'.input'][0]);s=reg(bn+'.start');r=reg(bn+'.result')
    assert len(b)==64 and all(0<=v<256 for v in b)
    ws,ss,actual=traces(b,s);assert actual==r,(t,i,j,'compression')
    assert s==(IV if not blocks else blocks[-1]['result'])
    blocks.append(dict(name=bn,input=b,start=s,result=r,ws=ws,ss=ss))
   assert D[full+'.message'][0]=='head.flatten ++ tail'
   assert D[full+'.head'][0]=='['+','.join(f'B{j:02}.input' for j in range(len(blocks)-1))+']'
   assert D[full+'.chunks'][0]==f'head ++ [B{len(blocks)-1:02}.input]'
   tail=json.loads(D[full+'.tail'][0]);message=sum([b['input'] for b in blocks[:-1]],[])+tail
   padded=message+[128]+[0]*((55-len(message))%64)+list((len(message)*8).to_bytes(8,'big'))
   assert padded==sum([b['input'] for b in blocks],[]),(t,i,'padding')
   result=blocks[-1]['result'];assert result==expected(expr),(t,i,'expected')
   assert hashlib.sha256(bytes(message)).digest()==b''.join(x.to_bytes(4,'big') for x in result)
   out.append(dict(tree=t,index=i,ns=ns,blocks=blocks,tail=tail,message=message))
 return out

def audit_all(text):
 out=[];pending=None
 for line in text.splitlines():
  if pending and not line.startswith(' '):
   if line==f'#print axioms {pending}':pending=None
   elif line.startswith(('theorem ','namespace ','end ')):
    out.append(f'#print axioms {pending}');pending=None
  out.append(line)
  if line.startswith('theorem '):pending=line.split()[1]
 assert pending is None
 return '\n'.join(out)+'\n'

def emit_chunk(rows,name):
 t=rows[0]['tree'];a=['import '+m for m in sorted({b['certificate'][0] for row in rows for b in row['blocks']})]+[f'import JHe_SHAEquations{t}','import JGz_HashTools','set_option autoImplicit false',f'namespace AspisR1.{name}','open JFp_SHA256']
 for row in rows:
  ns=row['ns'];i=row['index'];a += [f'namespace H{i:03}',f'open {ns}']
  for j,b in enumerate(row['blocks']):
   bn=f'B{j:02}';cm,cn=b['certificate']
   a += [f'namespace C{j:02}',f'theorem checked : compress {bn}.start (words {bn}.input)={bn}.result := {cm}.{cn}.checked',f'end C{j:02}']
  bs=row['blocks'];m=len(row['message']);blist='['+','.join(f'B{j:02}.input' for j in range(len(bs)))+']'
  # Small casts and padding tail computations only. No hash or compress reduction here.
  for j in range(len(bs)-1):a += [f'theorem cast{j:02} : (JGc_TX2_HashBytes.bytes B{j:02}.input).map Fin.val=B{j:02}.input := by rfl']
  a += [f'theorem tailCast : (JGc_TX2_HashBytes.bytes {ns}.tail).map Fin.val={ns}.tail := by rfl',f'theorem numeric : (JGc_TX2_HashBytes.bytes {ns}.message).map Fin.val={ns}.message := by',f'  simp only [{ns}.message,{ns}.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,'+','.join([f'cast{j:02}' for j in range(len(bs)-1)]+['tailCast'])+']']
  a += [f'theorem headLengths : ∀ b ∈ {ns}.head,b.length=64 := by', '  intro b hb',f'  change b ∈ ['+','.join(f'B{j:02}.input' for j in range(len(bs)-1))+'] at hb','  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb','  rcases hb with '+' | '.join(f'h{j}' for j in range(len(bs)-1))]
  for j in range(len(bs)-1):a += ['  · subst b; rfl']
  a += [f'theorem padded : pad {ns}.message={ns}.chunks.flatten := by',f'  have size : {ns}.message.length={m} := by',f'    simp only [{ns}.message,List.length_append]',f'    rw [JGz_HashTools.length_flatten _ headLengths]','    rfl',f'  have last : {ns}.tail ++ [128] ++ List.replicate {(55-m)%64} 0 ++ {lit(list((m*8).to_bytes(8,"big")))}=B{len(bs)-1:02}.input := by rfl','  unfold pad','  rw [size]',f'  rw [{ns}.message,{ns}.chunks]','  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]','  simp only [List.append_assoc] at last ⊢',f'  exact congrArg (List.append {ns}.head.flatten) last']
  a += [f'theorem lengths : ∀ b ∈ {ns}.chunks,b.length=64 := by',f'  intro b hb',f'  change b ∈ {blist} at hb','  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb','  rcases hb with '+' | '.join(f'h{j}' for j in range(len(bs)))]
  for j in range(len(bs)):a+= [f'  · subst b; rfl']
  a += [f'theorem hashed : JFp_SHA256.hash {ns}.message={ns}.result := by',f'  rw [JGz_HashTools.hash_chunks _ _ padded lengths]',f'  change {blist}.foldl (fun s b=>compress s (words b)) initial={ns}.result']
  for j in range(len(bs)):
   a += [f'  rw [List.foldl_cons,show '+('initial' if j==0 else f'B{j-1:02}.result')+f'=B{j:02}.start from rfl,C{j:02}.checked]']
  a += ['  rfl',f'theorem source : JFp_SHADigest.digest (JHe_SHAInputs{t}.input ⟨{i},by omega⟩)=JHe_SHAInputs{t}.expected ⟨{i},by omega⟩ := by',f'  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes {ns}.message).map Fin.val))=_','  rw [numeric,hashed]','  funext i','  fin_cases i <;> rfl','#print axioms source',f'end H{i:03}']
 a += [f'end AspisR1.{name}'];return audit_all('\n'.join(a)+'\n')

def emit_compute(bs,name):
 a=['import JFp_SHA256','set_option autoImplicit false',f'namespace AspisR1.{name}','open JFp_SHA256']
 for j,b in enumerate(bs):
  bn=f'B{j:03}';b['certificate']=(name,bn);a += [f'namespace {bn}',f'def input : List Nat := {lit(b["input"])}',f'def start : Reg := {rl(b["start"])}',f'def result : Reg := {rl(b["result"])}']
  for q in range(65):a += [f'def w{q:02} : List Nat := {lit(b["ws"][q])}',f'def s{q:02} : Reg := {rl(b["ss"][q])}']
  a += ['theorem checked : compress start (words input)=result := by','  have parsed : words input=w00 := by rfl','  rw [parsed]','  unfold compress loop','  change add start (constants.foldl transition (w00,s00)).2=result']
  for q,k in enumerate(K):a += [f'  have t{q:02} : transition (w{q:02},s{q:02}) {k}=(w{q+1:02},s{q+1:02}) := by rfl']
  a += ['  unfold constants']
  for q in range(64):a += [f'  rw [List.foldl_cons,t{q:02}]']
  a += ['  rfl','#print axioms checked',f'end {bn}']
 a += [f'end AspisR1.{name}'];return '\n'.join(a)+'\n'

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--size',type=int,default=32);ap.add_argument('--block-size',type=int,default=56);args=ap.parse_args();rows=collect();manifest=[];computations=[]
 allblocks=[b for row in rows for b in row['blocks']]
 groups=[allblocks[:16]]+[allblocks[i:i+28] for i in range(16,128,28)]+[allblocks[i:i+args.block_size] for i in range(128,len(allblocks),args.block_size)]
 for j,bs in enumerate(groups):
  name=f'JHx_Blocks{j:02}';content=emit_compute(bs,name);p=L/(name+'.lean')
  if args.check:assert p.read_text()==content,p
  else:p.write_text(content)
  computations.append(dict(module=name,blocks=len(bs),sha256=hashlib.sha256(content.encode()).hexdigest()))
 for t in range(3):
  rs=[r for r in rows if r['tree']==t]
  for start in range(0,len(rs),args.size):
   chunk=rs[start:start+args.size];name=f'JHx_T{t}C{start//args.size:02}';content=emit_chunk(chunk,name);p=L/(name+'.lean')
   if args.check:assert p.read_text()==content,p
   else:p.write_text(content)
   manifest.append(dict(module=name,tree=t,indices=[r['index'] for r in chunk],blocks=sum(len(r['blocks']) for r in chunk),sha256=hashlib.sha256(content.encode()).hexdigest()))
 assembly=['import JHe_SHARealization']+['import '+m['module'] for m in manifest]+['set_option autoImplicit false','namespace AspisR1.JHx_Instance','#check JHe_SHARealization','theorem source : JHe_SHARealization := by','  constructor']
 for t,n in enumerate([157,157,139]):
  assembly += ['  · intro i','    fin_cases i']
  for i in range(n):assembly += [f'    · exact JHx_T{t}C{i//args.size:02}.H{i:03}.source']
 assembly += ['#print axioms source','instance realization : JHe_SHARealization := source','#print axioms realization','end AspisR1.JHx_Instance']
 p=L/'JHx_Instance.lean';content='\n'.join(assembly)+'\n'
 if args.check:assert p.read_text()==content,p
 else:p.write_text(content)
 joint=(L/'JHw_Joint.lean').read_text().replace('import JHq_TX1\nimport JHn_Joint\nimport JHw_TX2','import JHw_Joint\nimport JHx_Instance').replace('namespace AspisR1.JHw_Joint','namespace AspisR1.JHx_Joint').replace('theorem source [trees : JHe_SHARealization]','theorem source')
 start=joint.index(' := by',joint.index('theorem source'))
 stop=joint.index('#print axioms source',start)
 joint=joint[:start]+' := by\n  exact JHw_Joint.source base stage slot runtime\n'+joint[stop:]
 joint=joint.replace('namespace AspisR1.JHx_Joint','namespace AspisR1.JHx_Joint\n#check JHe_SHARealization')
 joint=joint.replace('end AspisR1.JHw_Joint','end AspisR1.JHx_Joint')
 p=L/'JHx_Joint.lean'
 if args.check:assert p.read_text()==joint,p
 else:p.write_text(joint)
 report=dict(passed=True,equations=len(rows),compression_blocks=sum(len(r['blocks']) for r in rows),method='independent integer SHA256 compression, hashlib full digest, padding/chaining and input/expected association',source_pins=pins,chunk_size=args.size,block_size=args.block_size,computations=computations,manifest=manifest)
 (E/'JHx_GENERATOR_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ['passed','equations','compression_blocks','chunk_size']}))
if __name__=='__main__':main()
