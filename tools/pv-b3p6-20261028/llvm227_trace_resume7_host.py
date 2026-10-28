"""Read-only direct-call/global-reference/indirect-call inventory of shipped op227 LLVM."""
from pathlib import Path
import json,re,hashlib,lzma
from run import H
artifacts=json.loads((H/'llvm227-artifacts-resume7.json').read_text())
for package in ['aspis-statement','aspis-core','blake2']:
 q=H/('llvm227-'+package+'-artifacts-resume7.json')
 if q.exists():artifacts+=json.loads(q.read_text())['artifacts']
raws=[];origins=[];offset=0
for a in artifacts:
 b=Path(a['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==a['sha256']
 origins.append(dict(first_combined_line=offset+1,artifact=a));offset+=len(b.decode().splitlines())+1;raws.append(b)
raw=b'\n'.join(raws)
lines=raw.decode().splitlines();sy=r'@("[^"\n]+"|[-A-Za-z$._0-9]+)';funcs={};globals={};comment=''
i=0
while i<len(lines):
 line=lines[i]
 if line.startswith('; ') and not line.startswith('; Function Attrs:'):comment=line[2:]
 if line.startswith(('define ','declare ')):
  m=re.search(sy+r'\(',line)
  if not m:i+=1;continue
  name=m[1];start=i;body=[line]
  if name.startswith('llvm.'):comment='LLVM intrinsic '+name
  if line.startswith('define '):
   i+=1
   while lines[i]!='}':body.append(lines[i]);i+=1
   body.append('}')
  text='\n'.join(body);calls=[];indirect=[]
  for j,l in enumerate(body):
   if re.search(r'\b(call|invoke)\b',l):
    m1=re.search(r'\b(?:call|invoke)\b.*?'+sy,l)
    if m1:calls.append(dict(callee=m1[1],line=start+j+1,text=l))
    elif not l.lstrip().startswith(';'):indirect.append(dict(line=start+j+1,text=l))
  if name not in funcs or line.startswith('define '):
   funcs[name]=dict(name=name,description=comment,line=start+1,definition=line.startswith('define '),calls=calls,indirect=indirect,global_refs=sorted(set(re.findall(sy,text))),text=text)
 elif line.startswith('@'):
  m=re.match(sy,line)
  if m:globals[m[1]]=dict(line=i+1,text=line)
 i+=1
roots=[n for n,f in funcs.items() if f['definition'] and 'host_public13terminal_qm31' in n]
assert roots
seen=set();parents={}
def go(n):
 if n in seen:return
 seen.add(n)
 for c in funcs.get(n,{}).get('calls',[]):
  parents.setdefault(c['callee'],n);go(c['callee'])
for n in roots:go(n)
sinks=[];indirect=[];formats=[];usedglobals=set()
for n in sorted(seen):
 f=funcs.get(n)
 if not f:continue
 usedglobals.update(f['global_refs'])
 indirect += [dict(caller=n,**r)for r in f['indirect']]
 if any(k in f['description']+' '+n for k in ['fmt','write_str','write_char','write_fmt','_print','log::','to_string']):formats.append(dict(name=n,description=f['description'],line=f['line']))
 for c in f['calls']:
  target=funcs.get(c['callee'],{});desc=target.get('description','')+' '+c['callee']
  if any(s in desc for s in ['panic','abort','unwrap_failed','slice_index_fail']):
   pos=c['line']-f['line'];b=f['text'].splitlines();begin=pos
   while begin>0 and not re.match(r'^[^ ;].*:',b[begin]):begin-=1
   block=b[begin:pos+2]
   labels={}
   current=None
   for bl in b:
    match=re.match(r'^([^ ;][^:]*):',bl)
    if match:current=match[1];labels[current]=[]
    if current:labels[current].append(bl)
   prednames=re.findall(r'%([^ ,]+)',block[0].split('; preds =',1)[1]) if '; preds ='in block[0] else []
   sinks.append(dict(caller=n,caller_description=f['description'],callee_description=target.get('description',''),call=c,block=block,predecessor_blocks={pr:labels.get(pr,[])for pr in prednames}))
pending=list(usedglobals)
while pending:
 n=pending.pop()
 for ref in re.findall(sy,globals.get(n,{}).get('text','')):
  if ref not in usedglobals:usedglobals.add(ref);pending.append(ref)
fmtglobals=[dict(name=n,**g)for n,g in globals.items() if any(s in g['text']for s in ['write_str','write_char','write_fmt','fmt5Write'])]
result=dict(artifacts=artifacts,line_origins=origins,roots=[dict(name=n,description=funcs[n]['description'],line=funcs[n]['line'])for n in roots],reachable_functions=[dict(name=n,description=funcs.get(n,{}).get('description'),definition=funcs.get(n,{}).get('definition'),line=funcs.get(n,{}).get('line'))for n in sorted(seen)],call_edges=[dict(caller=n,**c)for n in sorted(seen)for c in funcs.get(n,{}).get('calls',[])],formatting_functions=formats,indirect_calls=indirect,panic_abort_calls=sinks,formatting_globals=fmtglobals,reachable_formatting_globals=[r for r in fmtglobals if r['name']in usedglobals],boundary='Static direct-call/reference inventory of freshly rebuilt shipped-crate LLVM under deployed configuration. External panic runtime is a sink, not recompiled or assumed silent. No binary identity claim.')
(H/'llvm227-trace-resume7.json').write_text(json.dumps(result,indent=2)+'\n')
# Preserve exact reachable definitions for independent review; LLVM is textual evidence.
subset='\n\n'.join(funcs[n]['text']for n in sorted(seen)if n in funcs)+'\n\n'+'\n'.join(g['text']for n,g in globals.items() if n in usedglobals)
with lzma.open(H/'llvm227-op227-resume7.ll.xz','wt')as z:z.write(subset)
(H/'llvm227-op227-resume7.ll.sha256').write_text(hashlib.sha256(subset.encode()).hexdigest()+'\n')
print(json.dumps(dict(roots=result['roots'],reachable=len(seen),formatting_functions=formats,indirect_calls=indirect,panic_abort_calls=[dict(caller=r['caller_description'],callee=r['callee_description'],line=r['call']['line'])for r in sinks],reachable_formatting_globals=len(result['reachable_formatting_globals']))))
