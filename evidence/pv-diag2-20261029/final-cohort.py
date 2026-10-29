"""Pre/post manifest input audit of the newly composed cohort; no recompilation."""
from pathlib import Path
import json,hashlib,re,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');mode=sys.argv[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();bad=[];rows=[]
cache=json.loads((D/'resume-cache-preflight.json').read_text());assert cache['mismatches']==[]
if mode=='pre':
 for m,r in cache['rows'].items():
  p=Path(r['path']);actual=sha(p) if p.is_file() else None
  if actual!=r['sha256']:bad.append(dict(module=m,path=str(p),expected=r['sha256'],actual=actual))
 latest={}
else:latest={}
for p in sorted(D.glob('lean630*-receipt.json')):
 r=json.loads(p.read_text())
 if r['exit']==0 and r.get('module'):latest[r['module']]=r
for m,r in sorted(latest.items()):
 src=D/'sources'/(m.replace('.','/')+'.lean');obj=D/'objects'/(m.replace('.','/')+'.olean')
 if sha(src)!=r['source_sha256'] or sha(obj)!=r['object_sha256']:bad.append(dict(module=m,reason='final source/object differs from accepted attempt',attempt=r['attempt']))
 for dep,files in r['dependency_objects'].items():
  for path,expected in files.items():
   p=Path(path);actual=sha(p) if p.is_file() else None
   if actual!=expected:bad.append(dict(module=m,dependency=dep,path=path,expected=expected,actual=actual))
 rows.append(dict(module=m,attempt=r['attempt'],source_sha256=sha(src),object_sha256=sha(obj),dependencies=r['dependency_objects']))
for p in D.glob('*-plan.json'):
 plan=json.loads(p.read_text())
 if 'module' not in plan or 'steps' not in plan:continue
 expected=plan['base']+'\n\n'+'\n\n'.join(plan['steps'])+'\nend PV_DIAG2\n';src=D/'sources'/(plan['module']+'.lean')
 if src.read_text()!=expected:bad.append(dict(module=plan['module'],reason='proof plan --check mismatch'))
for row in rows:
 if not row['module'].startswith('PV_DIAG2_'):continue
 src=(D/'sources'/(row['module']+'.lean')).read_text()
 if re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^\s*axiom\b|^\s*import XR|set_option (?:maxRecDepth|maxHeartbeats)',src,re.M):bad.append(dict(module=row['module'],reason='forbidden source construct'))
if mode=='post':
 for n in [63097,63098,63099]:
  r=json.loads((D/f'lean{n}-receipt.json').read_text());assert r['exit']==0
  out=(D/f'lean{n}-output.log').read_text();assert 'sorryAx' not in out and ': error' not in out
  for ax in re.findall(r'depends on axioms:\s*\[([^]]*)\]',out):assert set(x.strip() for x in ax.split(','))<={'propext','Classical.choice','Quot.sound'}
result=dict(phase=mode,h6_rows_checked=cache['checked'] if mode=='pre' else 'pre-check reused; new manifest imports and all their recorded dependencies checked below',modules=rows,mismatches=bad,source_revision=(D/'revision.txt').read_text().strip(),full_privacy_manifest_replayed=False)
(D/('final-cohort-'+mode+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(mode,'accepted own/generated modules',len(rows),'mismatches',len(bad));assert not bad
