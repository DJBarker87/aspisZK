import subprocess,json,re,hashlib,pathlib
out=pathlib.Path(__file__).parent
rev=subprocess.check_output(['git','rev-parse','research'],text=True).strip()
base='docs/research/v8-r0-zk-20261009/lean/'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,base],text=True).splitlines()
sources={p[len(base):-5]:subprocess.check_output(['git','show',rev+':'+p]).decode() for p in paths if p.endswith('.lean')}
def imports(s):
 return [m.replace('.','/') for line in s.splitlines() if line.startswith('import ') for m in line.split()[1:] if m.startswith(('R0Z.','R1Z.'))]
targets=['R1Z/SimCostOuterRetry6','R1Z/EventsR1P2']; chains={}
def visit(m,seen):
 if m in seen:return
 seen.add(m)
 for n in imports(sources.get(m,'')):visit(n,seen)
for t in targets:
 seen=set();visit(t,seen);chains[t]=sorted(seen)
mods=sorted(set(sum(chains.values(),[])))
remote='''import json,pathlib,hashlib
mods=json.loads(MODS)
b=pathlib.Path('/home/dombarker/project-offloads')
s=b/'aspis-joint-20261019/sources'; o=b/'aspis-joint-20261019/objects'
e=b/'aspis-fs-generic-20261006/evidence'
rows=[json.loads(l) for l in (e/'EJR_attempts.jsonl').read_text().splitlines()]
sent=(b/'r1-privacy-build-integration-20261019/evidence/sent.txt').read_text().splitlines()
r={}
for m in mods:
 p=s/(m+'.lean');q=o/(m+'.olean')
 r[m]={'rebuild_source_sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None,'object_exists':q.exists(),'object_sha256':hashlib.sha256(q.read_bytes()).hexdigest() if q.exists() else None,'EJR':[{k:v for k,v in x.items() if k in ['attempt','source_sha256','source_revision','lean_exit','validation_exit','deps']} for x in rows if x.get('module')==m], 'sent':[l for l in sent if len(l.split())>3 and l.split()[3]==m]}
 if m in ['R1Z/SimCostOuterRetry6','R1Z/EventsR1P2']:r[m]['source_text']=p.read_text()
print(json.dumps(r))
'''.replace('MODS',repr(json.dumps(mods)))
raw=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=remote.encode())
host=json.loads(raw)
for m,row in host.items():
 row['research_sha256']=hashlib.sha256(sources[m].encode()).hexdigest() if m in sources else None
 row['source_match']=row['research_sha256']==row['rebuild_source_sha256']
 row['imports']=imports(sources.get(m,''))
 if 'source_text' in row:(out/(m.split('/')[-1]+'.rebuild.lean.txt')).write_text(row.pop('source_text'))
(out/'audit.json').write_text(json.dumps({'research_revision':rev,'worktree_base':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'chains':chains,'modules':host},indent=2)+'\n')
lines=['# Research / rebuilt env-J source audit','',f'Research revision: `{rev}`. Read-only host inventory; no Lean attempts.','']
for t,chain in chains.items():
 lines += ['## '+t,'','Transitive R0Z/R1Z chain (including target):','']
 for m in chain:
  r=host[m];lines += [f"- `{m}` imports {', '.join(r['imports']) or '(no R0Z/R1Z imports)'}; source {'MATCH' if r['source_match'] else 'MISMATCH'}; shared object {'present' if r['object_exists'] else 'MISSING'}."]
lines+=['','## Exact source mismatches','']
for m,r in host.items():
 if not r['source_match']:lines += [f"- `{m}` research `{r['research_sha256']}`; rebuilt `{r['rebuild_source_sha256']}`; EJR "+str([(x.get('attempt'),x.get('source_sha256')) for x in r['EJR']])+'.']
lines += ['','Missing objects: '+', '.join('`'+m+'`' for m,r in host.items() if not r['object_exists']), '','Full per-module hashes, sent ledger entries, EJR source hashes and import adjacency: `audit.json`.']
(out/'AUDIT.md').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines[-15:]))
