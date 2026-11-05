"""Read-only frozen-source accessor and direct-call inventory. No native credit."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
paths=[p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'programs/aspis-pool/src'],text=True).splitlines() if p.endswith('.rs')]
functions=[];sources={};pins=[]
for p in paths:
 raw=subprocess.check_output(['git','show',REV+':'+p]);text=raw.decode();sources[p]=text
 local=Path(p)
 assert not local.exists() or local.read_bytes()==raw,('source drift',p)
 pins.append(dict(path=p,sha256=sha(raw),bytes=len(raw)))
 # Exclude test modules, retaining every production function in the prefix.
 text=text.split('#[cfg(test)]')[0]
 for m in re.finditer(r'\bfn\s+(\w+)\s*(?:<|\()',text):
  start=text.find('{',m.end());depth=1;i=start+1
  while depth and i<len(text):
   if text[i]=='{':depth+=1
   elif text[i]=='}':depth-=1
   i+=1
  functions.append(dict(path=p,name=m[1],line=text[:m.start()].count('\n')+1,end=text[:i].count('\n')+1,body=text[start:i]))
rows=[]
for f in functions:
 for m in re.finditer(r'\.data_is_empty\s*\(',f['body']):
  line=f['line']+f['body'][:m.start()].count('\n')
  callers=[]
  for parent in functions:
   for c in re.finditer(r'\b'+re.escape(f['name'])+r'\s*(?:::<[^;]*?>)?\s*\(',parent['body']):
    callers.append(dict(path=parent['path'],caller=parent['name'],line=parent['line']+parent['body'][:c.start()].count('\n')))
  rows.append(dict(path=f['path'],accessor_line=line,caller=f['name'],caller_line=f['line'],body_sha256=sha(f['body'].encode()),direct_callers=callers,status='OPEN',obligation='Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.',classification='liveness; no soundness claim'))
assert len(rows)==7
(E/'NIE_ACCESSORS.json').write_text(json.dumps(dict(frozen_revision=REV,method='conservative lexical direct-call inventory; imported aliases, cfg reachability and root association require separate review',accessors=rows,source_pins=pins),indent=2)+'\n')
prior=Path('evidence/pool-b3-20261106')
reuse=[]
for name in ['NHP_POOL_B.md','NHP_HANDOFF.md','NHP_REMAINING.md','NHP_STUBS.md','NHP_BRIDGES.md','NHP_DOMAINS.md','NHP_K086.json','NHP_K086-shape.json','NHP_EXPORT.json','NHP_CLOSED.json']:
 p=prior/name;reuse.append(dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size,mode='read-only citation; never rerun'))
(E/'NIE_REUSED_INPUTS.json').write_text(json.dumps(reuse,indent=2)+'\n')
print(json.dumps(dict(accessors=len(rows),direct_calls=sum(len(r['direct_callers']) for r in rows),native_credit=False)))
