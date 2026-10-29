"""Read-only h6 source/object/dependency audit; no library rebuilds."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');B=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((D/'resume-project-resolution.json').read_text());graph=json.loads((D/'project-graph.json').read_text());external={r['module'].replace('/','.'):r for r in json.loads((D/'external-authority.json').read_text())}
# Prefer one recorded coherent replay cohort. Each reused module is checked
# against its own recorded dependency hashes, not merely today's source.
C=B/'codex-pv-rjdec-20261028';records={}
for cohort in [B/'codex-pv-runjoin-20261026/runjoin32-lean',C]:
 for p in sorted((cohort/'evidence').glob('results-*.json')):
  for r in json.loads(p.read_text()):
   if r.get('accepted'):
    r['_source_path']=str(cohort/'sources'/(r['module'].replace('.','/')+'.lean'));records[r['module']]=r
P=B/'codex-pv-replay-20261027'
for line in (P/'evidence/results.jsonl').read_text().splitlines():
 r=json.loads(line);m=r['module'].replace('/','.')
 if m not in records and r.get('object_sha256'):
  r['dependencies']={d['module'].replace('/','.'):d for d in r['deps']}
  r['_source_path']=str(P/'sources'/(r['module']+'.lean'));records[m]=r
recovered=json.loads((D/'recovered-generation-chain.json').read_text())['sources']
rows={};bad=[];busy=set()
def visit(m):
 if m in rows:return rows[m]
 if m in busy:raise RuntimeError('cycle '+m)
 busy.add(m)
 if m in external:
  r=external[m];p=Path(r['path']);actual=sha(p) if p.is_file() else None
  out=dict(module=m,path=str(p),sha256=actual,authority='h4 external',expected=r['object_sha256'])
  if actual!=out['expected']:bad.append(out)
 elif m in records:
  r=records[m];pin=plan['modules'].get(m);s=Path(r['_source_path']);p=C/'objects'/(m.replace('.','/')+'.olean')
  out=dict(module=m,path=str(p),sha256=sha(p) if p.is_file() else None,source_sha256=sha(s) if s.is_file() else None,authority='h6 recorded rjdec',record_source_sha256=r['source_sha256'],expected=r['object_sha256'],record_dependencies=r['dependencies'])
  if m in recovered and out['source_sha256']!=recovered[m]['sha256']:bad.append(dict(module=m,reason='generation source mismatch'))
  if (pin and out['source_sha256']!=pin['sha256']) or (not pin and m not in graph) or out['source_sha256']!=r['source_sha256'] or out['sha256']!=r['object_sha256']:bad.append(out)
  if pin is None and m in graph and m not in recovered:
   gp=Path(graph[m]['path'])
   if not gp.is_file() or sha(gp)!=out['sha256']:bad.append(dict(module=m,reason='h7 graph object mismatch',path=str(gp),actual=out))
  for dep,old in r['dependencies'].items():
   got=visit(dep)
   if got.get('sha256')!=old['sha256']:bad.append(dict(module=m,dependency=dep,recorded=old,actual=got))
 elif m in plan['gaps'] and m in graph:
  # h7 graph object authority. All imports must resolve to exactly the graph
  # cohort, including library objects. No guessed source variant is installed.
  g=graph[m];p=Path(g['path']);out=dict(module=m,path=str(p),sha256=sha(p) if p.is_file() else None,authority='h7 graph',graph_entry=g)
  if not p.is_file():bad.append(out)
  for dep in g['imports']:
   got=visit(dep)
   gp=Path(graph[dep]['path']) if dep in graph else Path(external[dep]['path']) if dep in external else None
   if gp is None or not gp.is_file() or sha(gp)!=got.get('sha256'):bad.append(dict(module=m,dependency=dep,reason='graph cohort mismatch',graph_path=str(gp),actual=got))
 else:
  out=dict(module=m,reason='no source-matched recorded cache in chosen cohort',sha256=None)
  bad.append(out)
 rows[m]=out;busy.remove(m);return out

for root in ['R1Z.ProverRwRetryModel','R1Z.PDict_WireError','R1Z.ProverRwSuccessErrorSource','R1Z.PV_RunJoin_PreparedCaller32']:visit(root)
(D/'expanded-cache-preflight.json').write_text(json.dumps(dict(cohort=str(C),environment_sha256=sha(C/'J.json'),checked=len(rows),rows=rows,mismatches=bad),indent=2)+'\n')
print('cache closure',len(rows),'mismatches',len(bad));print(json.dumps(bad[:6],indent=2))
if not bad:
 O=D/'objects';O.mkdir(exist_ok=True)
 for m,r in rows.items():
  if m in external:continue
  dst=O/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():dst.symlink_to(r['path'])
 env=json.loads((C/'J.json').read_text());env['LEAN_PATH']=str(O)+':'+env['LEAN_PATH'];(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n')
else:raise SystemExit(1)
