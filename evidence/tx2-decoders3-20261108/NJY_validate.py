"""Strict local packet checks; no compiler/solver launches."""
from pathlib import Path
import hashlib,json,lzma,re,sys
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rs=[json.loads(l) for l in (E/'NJY_ATTEMPTS.jsonl').read_text().splitlines()];seen=set();stats={};errors=[];excluded=[];kani=[]
for r in rs:
 a=r['attempt'];assert a not in seen,a;seen.add(a);stats[r['kind']]=stats.get(r['kind'],0)+1
 for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','source_hashes']:assert k in r,(a,k)
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True,a
 assert r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-tx2-decoders3-20261107/NJY_target',a
 assert r['swaps'] in [0,'0'],a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,r.get('limits'))
 if r['kind']=='kani':
  g=json.loads((E/(a+'-graph-check.json')).read_text());l=json.loads((E/(a+'-lock-check.json')).read_text());assert g['graph_matches_frozen'] and g['all_features'] and l['unchanged'],a
  er=json.loads((E/(a+'-erasure-check.json')).read_text());assert er['passed'],a
  t=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  if r['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL' in t,a
  elif 'VERIFICATION:- FAILED' not in t or 'CBMC timed out' in t:
   finding=dict(attempt=a,reason='non-semantic failure; no control credit',exit=r['exit_status'])
   retired=E/(a+'_RETIRED.json')
   if retired.exists():
    rec=json.loads(retired.read_text());assert rec['status']=='TIMEOUT_NO_CREDIT' and rec['attempt']==a
    finding['retirement']=retired.name;excluded.append(finding)
   else:errors.append(finding)
  kani.append(dict(attempt=a,exit=r['exit_status'],semantic='VERIFICATION:-' in t,failed_checks=re.findall(r'Failed Checks: (.*)',t)))
idx=json.loads((E/'NJY_INPUTS.json').read_text())
for h,x in idx['objects'].items():
 p=E/x['path'];assert sha(p.read_bytes())==x['archive_sha256'];assert sha(lzma.decompress(p.read_bytes()))==h
for a,inputs in idx['attempts'].items():
 if a not in seen:continue
 r=next(r for r in rs if r['attempt']==a)
 for n,h in r['source_hashes'].items():assert inputs[n]==h,(a,n)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
for p in E.glob('NJY_*.lean'):
 t=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',t),p
out=dict(attempts=stats,errors=errors,excluded_failures=excluded,kani=kani,max_rss_kib=max(int(r['peak_rss_kib']) for r in rs),scope_wall_seconds=sum(r['wall_seconds'] for r in rs),budget=dict(kani_limit=90,lean_limit=90,extraction_limit=1),source_inputs=len(idx['objects']))
(E/'NJY_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='kani'}));sys.exit(bool(errors))
