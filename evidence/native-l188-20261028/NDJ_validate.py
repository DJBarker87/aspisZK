#!/usr/bin/env python3
"""Validate every manifest pin/count from immutable evidence; fail closed.

No Lean/Kani/build launch. Live host rehash is the default; --offline only
checks the retained host-hash receipt and explicitly reports that limit.
"""
from pathlib import Path
import json,hashlib,lzma,subprocess,sys,time,resource,re
import NDJ_manifest as m
E=m.E;R=m.R
start=time.monotonic()
def ensure(b,message):
 if not b:raise AssertionError(message)
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def blobpins(pins):
 proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for p,v in pins.items():
  proc.stdin.write((v['revision']+':'+p+'\n').encode());proc.stdin.flush();meta=proc.stdout.readline().split();ensure(len(meta)==3 and meta[1]==b'blob',p)
  size=int(meta[2]);left=size;h=hashlib.sha256()
  while left:
   b=proc.stdout.read(min(left,1024*1024));ensure(bool(b),p);h.update(b);left-=len(b)
  ensure(proc.stdout.read(1)==b'\n',p);ensure(h.hexdigest()==v['sha256'],('git hash',p));ensure(size==v['bytes'],('git size',p))
 proc.stdin.close();ensure(proc.wait()==0,'git exit')
try:
 d=m.obj('evidence/native-l188-20261028/NDJ_RELEASE_MANIFEST.json')
 ensure(d==m.derive(),'manifest differs from recomputed evidence')
 ensure((E/'NDJ_RELEASE_MANIFEST.md').read_text()==m.markdown(d),'markdown differs')
 index=json.loads((E/'NDJ_EVIDENCE_PINS.json').read_text());blobpins(index['git'])
 for p,v in index['local'].items():
  b=(R/p).read_bytes();ensure(m.sha(b)==v['sha256'] and len(b)==v['bytes'],('local evidence pin',p))
 sourcepins={p:dict(revision=d['frozen_source_revision'],sha256=h,bytes=len(git('show',d['frozen_source_revision']+':'+p))) for p,h in d['frozen_source_pins'].items()}
 blobpins(sourcepins)
 ensure(len(d['game_clauses'])==13 and len({g['id'] for g in d['game_clauses']})==13,'game clause count')
 ensure(d['query_parameter']['row']=='L154' and d['extraction_status'].startswith('TRUST'),'parameter/trust classification')
 ensure(not d['combined_replay_success'] and d['separate_roots_pass'],'failed shared environment must remain visible')
 pins=json.loads(lzma.decompress((E/'NDJ_CACHE_PINS.json.xz').read_bytes()))
 ensure(m.sha(lzma.decompress((E/'NDJ_CACHE_PINS.json.xz').read_bytes()))==(E/'NDJ_CACHE_PINS.json.sha256').read_text().strip(),'compressed cache pins')
 selections={k:{r['module']:r for r in pins['objects'] if r['selection']==k} for k in ['joint','union']}
 all_artifacts={a['path']:a for row in pins['objects'] for a in row['artifacts']}
 actual=set()
 attempt_rows=[json.loads(line) for line in (E/'NDJ_ATTEMPTS.jsonl').read_text().splitlines()]
 for name in ['NDJ_R001','NDJ_R002','NDJ_R003','NDJ_R004']:
  ensure(any(r.get('kind')=='admission' and r.get('attempt')==name and r.get('allowed') is True and r.get('exit_status')==0 for r in attempt_rows),('admission exit/allowed',name))
 for a in d['audit_attempts']:
  receipt=m.obj('evidence/native-l188-20261028/'+a['attempt']+'/receipt.json')
  for src,h in receipt['source_hashes'].items():ensure(m.sha((E/Path(src).name).read_bytes())==h,('attempt source',src))
  ensure(a['swap']==0 and receipt['limits']['memory.swap.max']=='0' and receipt['limits']['pids.max']=='64','resource limits')
  admission=m.obj('evidence/native-l188-20261028/'+a['attempt']+'-reservation.json');ensure(admission['allowed'] is True,'admission denied')
  if a['exit_status']!=0:continue
  ensure(set(a['roots'][0]['axioms'])==m.STANDARD,'nonstandard reachable axiom')
  selected=selections['joint' if a['target']=='JHx_Joint' else 'union']
  config=m.obj('evidence/native-l188-20261028/'+a['attempt']+'.json')
  # The lead-owned agg16 shim records only its direct-import pin subset in
  # the final receipt. The submitted config retains the complete preflight
  # selection; both are checked against the live full-object census.
  config_objects=config['deps_fingerprint']['selected_objects']
  for name,v in receipt['deps_fingerprint']['selected_objects'].items():
   ensure(v['path'] in all_artifacts and all_artifacts[v['path']]['sha256']==v['sha256'],('runner direct-import pin',name))
  for name in a['closure_modules']:
   ensure(name in selected,('unpinned actual module',name));v=selected[name]
   ensure(config_objects[name]['sha256']==v['sha256'],('selected object mismatch',name))
  actual.update(a['closure_modules'])
 ensure(len(actual)==d['union_module_count'],'closure union count')
 ensure(d['budget']['normal_lean_used']<=6 and d['budget']['agg16_used']==1 and d['budget']['kani_used']==0,'budget')
 expected=m.obj('evidence/joint-agg2-20261028/JHw_RUNNER_HASHES.json')['sha256'];ensure(m.obj('evidence/native-l188-20261028/NDJ_AGG16_RUNNER_HASHES.json')==expected,'agg16 runner pins')
 # Revalidate baseline and explicit later research snapshot using the unchanged
 # NCZ engine. This cannot silently grant credit to a newly discovered report.
 before={p:m.sha((E/p).read_bytes()) for p in ['NDJ_NCZ_SNAPSHOT.json','NDJ_COVERAGE.json']}
 run=subprocess.run([sys.executable,str(E/'NDJ_coverage.py'),'--check'],capture_output=True,text=True,cwd=R)
 ensure(run.returncode==0,'NCZ recomputation: '+run.stderr)
 ensure(all(m.sha((E/p).read_bytes())==h for p,h in before.items()),'NCZ snapshot changed')
 ndk=subprocess.run([sys.executable,str(E/'NDJ_NDK.py'),'--check'],capture_output=True,text=True,cwd=R)
 ensure(ndk.returncode==0,'NDK recomputation: '+ndk.stderr)
 host=json.loads(lzma.decompress((E/'NDJ_HOST_VERIFICATION.json.xz').read_bytes()))
 ensure(host['exit_status']==0 and not host['errors'],'retained host verification failed')
 ensure(m.sha(lzma.decompress((E/'NDJ_HOST_VERIFICATION.json.xz').read_bytes()))==(E/'NDJ_HOST_VERIFICATION.json.sha256').read_text().strip(),'host receipt compression')
 live='--offline' not in sys.argv
 if live:
  r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3 -'],input=(E/'NDJ_host_verify.py').read_text(),capture_output=True,text=True)
  ensure(r.returncode==0,'host hash audit failed: '+r.stderr+r.stdout[:1000]);h=json.loads(r.stdout)
  ensure(h['checked']==host['checked'] and h['elves']==host['elves'] and not h['errors'],'live host pin mismatch')
 # No committed / deliverable artifact may exceed the required20MiB limit.
 for p in E.rglob('*'):
  if p.is_file():ensure(p.stat().st_size<=20*1024*1024,('oversized file',str(p)))
 usage=resource.getrusage(resource.RUSAGE_SELF)
 child_usage=resource.getrusage(resource.RUSAGE_CHILDREN)
 report=dict(exit_status=0,target='NDJ release manifest consistency, hashes, pins, counts, NCZ snapshots and host artifact/object rehash',wall_seconds=time.monotonic()-start,peak_rss_bytes=max(usage.ru_maxrss,child_usage.ru_maxrss),peak_rss_metric='maximum process high-water RSS including sequential children; Darwin bytes',swap=usage.ru_nswap+child_usage.ru_nswap,source_revision=git('rev-parse','HEAD').decode().strip(),print_axioms='No new theorem: exact per-root #print axioms in NDJ_R002 and NDJ_R004',git_evidence_files=len(index['git']),local_evidence_files=len(index['local']),frozen_source_files=len(sourcepins),host_files=host['checked_files'],live_host_rehash=live,closure_module_count=d['union_module_count'],status=d['status'])
 print(json.dumps(report,indent=2));sys.exit(0)
except Exception as e:
 print('NDJ validation FAILED: '+str(e),file=sys.stderr);sys.exit(1)
