"""Syntax-only parameterization of fresh frozen resume; opaque functions remain parameters."""
from pathlib import Path
import json,lzma,base64,re,hashlib,difflib
E=Path(__file__).resolve().parent
payload=json.loads(lzma.decompress((E/'NID_EXTRACT_OUTPUTS.json.xz').read_bytes()))
raw=lambda n:base64.b64decode(payload['raw/NHR_tx2_common/'+n+'.lean']['base64']).decode()
types=raw('Types');funs=raw('Funs');ext=raw('FunsExternal_Template')
mapping=[];variables=[]
for i,(name,sig) in enumerate(re.findall(r'^axiom\s+(\S+)\s*([\s\S]*?)(?=\n/--|\Z)',ext,re.M)):
 sig=sig.strip();depth=0;colon=None
 for j,ch in enumerate(sig):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:colon=j;break
 assert colon is not None
 bind=sig[:colon].strip();ty=sig[colon+1:].strip();var='NID_call_'+str(i)
 variables.append('variable ('+var+' : '+(('∀ '+bind+',\n') if bind else '')+ty+')')
 mapping.append(dict(generated_name=name,parameter=var,signature=sig))
adapted=re.sub(r'\bdiscriminant isize,?\s*','',types);adapted=re.sub(r'@\[\]\s*\n','',adapted)
funs=funs.replace('import NHR_tx2_common.FunsExternal\n','').replace('import NHR_tx2_common.Types','import NID_ResumeEmissionTypes')
funs=funs.replace('namespace NHR_tx2_common\n','namespace NHR_tx2_common\n'+'\n\n'.join(variables)+'\n',1)
for m in sorted(mapping,key=lambda x:-len(x['generated_name'])):
 funs=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(m['generated_name'])+r'(?![A-Za-z0-9_.])',m['parameter'],funs)
adapted=adapted.replace('NHR_tx2_common','NID_ResumeEmission');funs=funs.replace('NHR_tx2_common','NID_ResumeEmission')
funs+='\n#print axioms NID_ResumeEmission.verifier.resume\n#print axioms NID_ResumeEmission.verifier.candidate.tx2_common\n'
for stem,before,after in [('Types',types,adapted),('Funs',raw('Funs'),funs)]:
 name='NID_ResumeEmission'+stem
 (E/(name+'.lean')).write_text(after)
 (E/(name+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='raw/'+stem+'.lean',tofile=name+'.lean')))
(E/'NID_RESUME_EMISSION_INTERFACE.json').write_text(json.dumps(dict(parameters=mapping,raw_hashes={k:v['sha256'] for k,v in payload.items() if k.startswith('raw/')},changes='namespace/module retarget, remove duplicate discriminant registrations, exact NHR parameterization of opaque declarations; no callee laws or successful body premise'),indent=2)+'\n')
# Parameterize references to generated helper definitions transitively.  Their
# implicit section parameters become explicit leading arguments in declaration order.
pat=re.compile(r'^def\s+(\S+)',re.M)
chunks=list(pat.finditer(funs));deps={};segments={}
for i,m in enumerate(chunks):
 end=chunks[i+1].start() if i+1<len(chunks) else funs.index('\n#print axioms')
 segments[m[1]]=funs[m.end():end]
 deps[m[1]]=set(map(int,re.findall(r'\bNID_call_(\d+)\b',segments[m[1]])))
for _ in chunks:
 changed=False
 for name,s in segments.items():
  more=set().union(*(v for n,v in deps.items() if n!=name and re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w.])',s)),set())
  if not more<=deps[name]:deps[name]|=more;changed=True
 if not changed:break
# Rebuild each declaration segment, never rewrite its own declared identifier.
out=funs[:chunks[0].start()]
for i,m in enumerate(chunks):
 s=segments[m[1]]
 for name in sorted(deps,key=len,reverse=True):
  if not deps[name]:continue
  args=' '.join('NID_call_'+str(j) for j in sorted(deps[name]))
  s=re.sub(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])','('+name+' '+args+')',s)
 out+=funs[m.start():m.end()]+s
out+=funs[funs.index('\n#print axioms'):]
(E/'NID_ResumeEmissionFuns.lean').write_text(out)
(E/'NID_ResumeEmissionFuns.diff').write_text(''.join(difflib.unified_diff(raw('Funs').splitlines(True),out.splitlines(True),fromfile='raw/Funs.lean',tofile='NID_ResumeEmissionFuns.lean')))
x=json.loads((E/'NID_RESUME_EMISSION_INTERFACE.json').read_text());x['transitive_arguments']={n:sorted(v) for n,v in deps.items()};(E/'NID_RESUME_EMISSION_INTERFACE.json').write_text(json.dumps(x,indent=2)+'\n')
# Keep the stricter NID source gate: no per-module heartbeat/recursion overrides.
for stem in ['Types','Funs']:
 p=E/('NID_ResumeEmission'+stem+'.lean');text=p.read_text();text=re.sub(r'^set_option max(?:Heartbeats|RecDepth) \d+\n','',text,flags=re.M);p.write_text(text)
 (E/('NID_ResumeEmission'+stem+'.diff')).write_text(''.join(difflib.unified_diff(raw(stem).splitlines(True),text.splitlines(True),fromfile='raw/'+stem+'.lean',tofile=p.name)))
