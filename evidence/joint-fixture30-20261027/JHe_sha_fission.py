from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2]; L=R/'lean'; P=Path(__file__).resolve().parent
check='--check' in sys.argv
outputs={}; inputs={}; pairs=[]; request_data={}
def read(p):
 s=p.read_text();inputs[str(p.relative_to(R))]=hashlib.sha256(s.encode()).hexdigest();return s
mapping={f'JHc_Tree{t}Part{k}':f'JHe_C_Tree{t}' for t in range(3) for k in ['0','1','2','3','4A','4B','4','5','6','7']}
for n in ['RootReads','Batch','PreBatch','BatchFrontier','TX1Candidate']:mapping['JHc_'+n]='JHe_C_'+n
def rename(s):
 # Every non-module namespace of the three cloned trees is prefixed too.
 s=s.replace('JHc_Gr_','JHe_C_Gr_').replace('JHc_Gu_','JHe_C_Gu_').replace('JHc_Gw_','JHe_C_Gw_').replace('JHc_Gy_','JHe_C_Gy_')
 for a,b in sorted(mapping.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
 return s
# Retain only literal data declarations, never a compression theorem.
data={t:['import JFp_SHABlocks','import JFp_SHADigest','import JGc_TX2_HashBytes','import '+['JGf_TX2_M0Root','JGh_TX2_M1Root','JGc_TX2_M2Root'][t],'set_option autoImplicit false'] for t in range(3)}
for p in sorted(L.glob('JHc_Certs*.lean')):
 t=int(p.stem.split('Certs')[1].split('_')[0]);ss=read(p)
 for line in ss.splitlines():
  if line.startswith(('namespace ','open ','end','def ')):
   if line.startswith('def '):assert ':=' in line and line.split(':=',1)[1].strip(),(p,line)
   data[t].append(rename(line))
for t in range(3):
 for p in sorted(L.glob(f'JHc_Tree{t}Part*.lean')):
  ss=read(p)
  for n in re.findall(r'^theorem hash(\d+)\s*:',ss,re.M):
   pairs.append((t,n))
   inp=re.search(r'^def input'+n+r' : Bytes := (.+)$',ss,re.M).group(1)
   out=re.search(r'^def value'+n+r' : State := (.+)$',ss,re.M).group(1)
   assert ('.message' in inp and '.result' in out) or ('Roots.input' in inp and 'Roots.value' in out),(t,n,inp,out)
   request_data[(t,n)]=(rename(inp),rename(out))
assert len(pairs)==len(set(pairs))==453
for t in range(3):
 realization=['namespace AspisR1',f'class JHe_SHA{t} : Prop where']
 for tree,n in pairs:
  if tree==t:
   inp,out=request_data[(t,n)]
   realization.append(f'  t{t}_{n} : JFp_SHADigest.digest ({inp})=({out})')
 realization.append('end AspisR1')
 outputs[f'JHe_SHAEquations{t}.lean']='\n'.join(data[t]+realization)+'\n'
aggregate=[f'import JHe_SHAEquations{t}' for t in range(3)]+['set_option autoImplicit false','namespace AspisR1','/-- Exactly453 concrete batch SHA equations, partitioned to keep record elaboration bounded. -/','class JHe_SHARealization : Prop where']
aggregate += [f'  tree{t} : JHe_SHA{t}' for t in range(3)]
aggregate += [f'instance [s : JHe_SHARealization] : JHe_SHA{t} := s.tree{t}' for t in range(3)]
aggregate += ['end AspisR1']
outputs['JHe_SHARealization.lean']='\n'.join(aggregate)+'\n'
# Drop only the now-unused normalization witnesses; replace SHA proofs by fields.
def transform_body(s,t=None):
 lines=s.splitlines();out=[];i=0
 while i<len(lines):
  line=lines[i]
  if line.startswith('import '):i+=1;continue
  m=re.match(r'theorem ((?:cast\d+_\d+|tail\d+|numeric\d+))\s*:',line)
  h=re.match(r'theorem hash(\d+)\s*:',line)
  if m or h:
   j=i+1
   while j<len(lines) and not re.match(r'^(?:theorem |def |namespace |end(?:\s|$)|#print |set_option |noncomputable |open |attribute )',lines[j]):j+=1
   if h:
    assert t is not None
    header=line.split(':=',1)[0]
    assert ':=' in line,(t,line)
    out.append(header+f':= JHe_SHA{t}.t{t}_{h.group(1)}')
   i=j
   if m and i<len(lines) and lines[i].startswith('#print axioms '+m.group(1)):i+=1
   continue
  out.append(line);i+=1
 return rename('\n'.join(out))
for t in range(3):
 files=sorted(L.glob(f'JHc_Tree{t}Part*.lean'));imports={'JHe_SHARealization'};bodies=[]
 for p in files:
  s=read(p)
  for imp in re.findall(r'^import (\S+)',s,re.M):
   if imp.startswith('JHc_Certs') or imp.startswith(f'JHc_Tree{t}Part'):continue
   imports.add(rename(imp))
  bodies.append(transform_body(s,t))
 outputs[f'JHe_C_Tree{t}.lean']='\n'.join('import '+x for x in sorted(imports))+'\nsection\nvariable [sha : AspisR1.JHe_SHARealization]\n'+'\n'.join(bodies)+'\nend\n'
for n in ['RootReads','Batch','PreBatch','BatchFrontier','TX1Candidate']:
 s=read(L/f'JHc_{n}.lean');imports={rename(x) for x in re.findall(r'^import (\S+)',s,re.M)}
 imports.add('JHe_SHARealization')
 outputs[f'JHe_C_{n}.lean']='\n'.join('import '+x for x in sorted(imports))+'\nsection\nvariable [sha : AspisR1.JHe_SHARealization]\n'+transform_body(s)+'\nend\n'
for name,s in outputs.items():
 seen_command=False
 for line in s.splitlines():
  if line.startswith('import '):assert not seen_command,(name,'late import')
  elif line.strip():seen_command=True
 if check:assert (L/name).read_text()==s,name
 else:(L/name).write_text(s)
manifest=dict(source_inputs=inputs,outputs={n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()},sha_equations=len(pairs),request_data={f'{t}_{n}':v for (t,n),v in request_data.items()},proof_hypothesis='AspisR1.JHe_SHARealization',scope='Exact batch mathematical SHA equations only; no acceptance field; original query/flush/writer proofs reused unchanged')
(P/'JHe_SHA_FISSION.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(check=check,modules=len(outputs),sha_equations=len(pairs))))
