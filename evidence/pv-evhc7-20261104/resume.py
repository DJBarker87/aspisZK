"""D593: finish two rebuilds in the fresh D578 overlay, then NER_SCAN only."""
from pathlib import Path
import hashlib, json, lzma, os, re, subprocess, sys, time

E = Path(__file__).resolve().parent
B = E.parent / 'codex-pv-evhc6-20261103'
R = E.parent
os.chdir(E)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def save(p, v): Path(p).write_text(json.dumps(v, indent=2) + '\n')
p = read(B/'PLAN.json')
auth = read(E/'RESUME-AUTHORIZATION.json')
assert sha(B/'BLOCKED.json') == auth['prior_sha256']
assert str(B/'objects') == auth['overlay']
assert sha(p['sysroot']+'/bin/lean') == read(B/'NER_STREAM_B_COHORT_META.json')['lean_binary_sha256']
prior = [read(f) for f in B.glob('lean-*/receipt.json')]
assert all(v['exit_status'] == 0 or v['attempt'] == 'lean-91400' for v in prior)
done = {v['module'] for v in prior if v['exit_status'] == 0 and v['module'] in p['order']}
pending = [m for m in p['order'] if m not in done]
assert len(done) == 592 and pending == ['PV_BR_PV_EVH_Residual', 'PV_BR_PV_EVH_Deployed']
# Global collision inventory: job-root configs/admissions and receipt directories.
used = []
for job in R.glob('codex-*'):
 for f in job.iterdir():
  if re.search(r'(?<![0-9])920[0-5][0-9](?![0-9])',f.name):
   used.append(str(f))
sent = R/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():
 for line in sent.read_text().splitlines():
  fields=line.split()
  if len(fields)>2 and fields[2].isdigit() and 92000<=int(fields[2])<=92059: used.append(line)
assert not used, used
save('ID-AUDIT.json', dict(range=[92000,92059], collisions=used))
q = R/'QUIET_WINDOW.json'
save('QUIET-WINDOW.json', dict(marker=read(q) if q.exists() else None, epoch=time.time()))

def launch(a, cfg, runner):
 assert 92000 <= a <= 92059
 cfg['attempt'] = f'lean-{a}'
 cfgfile = f'attempt-{a}.json'
 save(cfgfile, cfg)
 for retry in range(11):
  admission = f'admission-{a}-{retry}.json'
  with open(f'admission-{a}-{retry}.log','w') as log:
   r = subprocess.run(['python3',str(R/'codex-pv-runjoin-20261026/reservation-existing.py'),admission],stdout=log,stderr=subprocess.STDOUT)
  v = read(admission) if Path(admission).exists() else None
  if r.returncode == 0 and v and v.get('allowed') is True: break
  save(f'refusal-{a}-{retry}.json',dict(epoch=time.time(),admission=admission,exit_status=r.returncode,compiler_started=False,slot_consumed=False,authorization='D593 explicit pre-compilation refusal exemption'))
  if v and v.get('allowed') is False:
   print('REFUSED',a,retry,flush=True)
   if retry == 10: raise RuntimeError('admission retry budget exhausted')
   time.sleep(180)
  elif v is None and retry == 0:
   time.sleep(30)
  else: raise RuntimeError(('admission infrastructure failure',a,retry))
 print('START',a,cfg['module'],flush=True)
 with open(f'launch-{a}.log','w') as log:
  r = subprocess.run(['systemd-run','--user','--scope','--quiet',f'--unit=pv-evhc7-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(E/runner),cfgfile],stdout=log,stderr=subprocess.STDOUT)
 receipt = read(f'lean-{a}/receipt.json')
 print('DONE',a,receipt['exit_status'],receipt['wall_seconds'],receipt['peak_rss_kib'],flush=True)
 if r.returncode or receipt['exit_status'] or receipt['wall_seconds']>=600 or int(receipt['peak_rss_kib'] or 0)>7*1024*1024:
  save('STOP.json',dict(id=a,receipt=f'lean-{a}/receipt.json',reason='failed scope or mandatory resource review; no retry',launch_exit=r.returncode))
  sys.exit(1)
 return receipt

for a,m in zip(range(92000,92050),pending):
 assert all(d not in p['sources'] or d in done for d in p['edges'][m])
 src = 'sources/'+m.replace('.','/')+'.lean'
 assert sha(B/src) == p['sources'][m]['sha256']
 target = E/src; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes((B/src).read_bytes())
 # Actual first-root resolution, with every direct import pinned by the runner.
 for dep in p['edges'][m]:
  top=dep.split('.')[0]
  root=next(Path(r) for r in p['LEAN_PATH'].split(':') if (Path(r)/top).is_dir() or (Path(r)/(top+'.olean')).is_file())
  assert root==B/'objects',dep
  assert (root/(dep.replace('.','/')+'.olean')).is_file(),dep
 out=B/'objects'/(m.replace('.','/')+'.olean')
 assert not out.exists(), m
 assert not any(sha(target) in v.get('source_hashes',{}).values() for v in prior if v['exit_status']!=0)
 cfg=dict(kind='lean',module=m,mechanical_reconciliation=True,charged_proof_attempt=False,sources=[src],env=dict(LEAN_PATH=p['LEAN_PATH']),timeout=600,command=[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',str(out),src],source_revision=p['sources'][m]['revision'],deps_fingerprint=dict(authority_manifest_sha256=sha(B/'NER_STREAM_B_COHORT.jsonl.xz'),plan_sha256=sha(B/'PLAN.json'),ruling="D593 resume; D578 h6'' coherent NER fresh overlay"),expected_time='mechanical focused recompilation; no source/proof change')
 prior.append(launch(a,cfg,'S2W_lean_host.py'));done.add(m)
save('BUILDS-COMPLETE.json',dict(status='PASS',rebuilt=len(done),new_rebuilds=2,prior_rebuilds=592,overlay=str(B/'objects')))

# Hash every selected object and companion; authority remains immutable.
cohort=[json.loads(l) for l in lzma.decompress((B/'NER_STREAM_B_COHORT.jsonl.xz').read_bytes()).splitlines()]
authority={r['module']:r for r in cohort}
expected={r['module']:r['imports'] for r in cohort}|p['edges']
rows=[]
for m,deps in expected.items():
 obj=B/'objects'/(m.replace('.','/')+'.olean')
 assert obj.is_file() and not obj.is_symlink() and obj.stat().st_nlink==1,m
 artifacts=[]
 for f in [obj,Path(str(obj)+'.server'),Path(str(obj)+'.private'),obj.with_suffix('.ir')]:
  if f.exists():
   assert not f.is_symlink() and f.stat().st_nlink==1,str(f)
   artifacts.append(dict(path=str(f),sha256=sha(f),bytes=f.stat().st_size))
 if m in authority:
  assert artifacts[0]['sha256']==authority[m]['object_sha256'],m
  for cp in authority[m]['companions']: assert any(a['sha256']==cp['sha256'] for a in artifacts),cp
 else:
  rs=[v for v in prior if v.get('module')==m and v['exit_status']==0]
  assert len(rs)==1,m
  assert rs[0]['source_hashes']['sources/'+m.replace('.','/')+'.lean']==p['sources'][m]['sha256']
 rows.append(dict(module=m,imports=deps,artifacts=artifacts,rebuilt=m in p['sources'],source=p['sources'].get(m,{})))
with open('COMBINED-MANIFEST.jsonl','w') as f:
 for row in rows:f.write(json.dumps(row,separators=(',',':'))+'\n')
print('MANIFEST PINNED',len(rows),flush=True)
roots=list(dict.fromkeys(['RPx_Deployed']+p['consumer_imports']))
save('SCAN-ROOTS.json',roots)
closure=set()
def visit(m):
 if m in closure:return
 assert m in expected,m
 closure.add(m)
 for d in expected[m]:visit(d)
for m in roots:visit(m)
save('EXPECTED-SCAN-MODULES.json',sorted(closure))
helper=read(B/'lean-91390/receipt.json')
assert helper['exit_status']==0 and helper['source_hashes']['PV_NER_Scan.lean']==sha('PV_NER_Scan.lean')
save('SCANNER-HELPER-REUSE.json',dict(receipt=str(B/'lean-91390/receipt.json'),sha256=sha(B/'lean-91390/receipt.json'),print_axioms=helper['print_axioms'],classification='summary-based #print axioms; unchanged helper compile reused'))
cfg=dict(kind='lean',module='PV_NER_Scan_run',sources=['PV_NER_Scan.lean','SCAN-ROOTS.json','EXPECTED-SCAN-MODULES.json','COMBINED-MANIFEST.jsonl'],env=dict(LEAN_PATH=p['LEAN_PATH']),timeout=600,command=[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','--run','PV_NER_Scan.lean'],source_revision=read(B/'AUTHORITY.json')['workspace_revision'],deps_fingerprint=dict(lean_binary_sha256=sha(p['sysroot']+'/bin/lean'),manifest_sha256=sha('COMBINED-MANIFEST.jsonl'),plan_sha256=sha(B/'PLAN.json'),scanner_method='NER_FinalDriverV2 active private checked declarations, types, values, recursor rules and metadata; stable first-occurrence imports; loadExts=false'),expected_time='combined closure active-kernel import and scan; no elaborator extension caches')
launch(92050,cfg,'S2W_run_host.py')
scan=[json.loads(l) for l in Path('COMBINED-SCAN-ROWS.jsonl').read_text().splitlines()]
assert {r['module'] for r in scan}==closure
assert all(r['imports_match'] and not r['dangling'] for r in scan)
save('SCAN.json',dict(status='coherent',module_count=len(scan),dangling_references=0,dangling_modules=[],imports_all_match=True,declarations=sum(r['declarations'] for r in scan),edges=sum(r['edges'] for r in scan),rows_sha256=sha('COMBINED-SCAN-ROWS.jsonl'),receipt='lean-92050/receipt.json',method='NER_FinalDriverV2 referenceNames + loadedScan; active private kernel; extensions disabled',consumer_body_checked=False,full_consumer_dependencies_scanned=True))
print('SCAN ZERO DANGLING',len(scan),flush=True)
