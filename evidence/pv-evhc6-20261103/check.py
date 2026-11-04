"""Focused scanner compilation then combined-closure private-kernel scan."""
from pathlib import Path
import hashlib,json,subprocess,os,lzma,sys
B=Path(__file__).resolve().parent;os.chdir(B);R=B.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
p=json.load(open('PLAN.json'));assert json.load(open('BUILDS-COMPLETE.json'))['status']=='PASS'
lean_binary_sha256=sha(p['sysroot']+'/bin/lean');assert lean_binary_sha256==json.load(open('NER_STREAM_B_COHORT_META.json'))['lean_binary_sha256']
cohort=[json.loads(l) for l in lzma.decompress(Path('NER_STREAM_B_COHORT.jsonl.xz').read_bytes()).splitlines()];authority={r['module']:r for r in cohort}
# Re-pin every artifact after builds; compare all authority hashes to exact original pins.
rows=[];expected={r['module']:r['imports'] for r in cohort}|p['edges']
for m,deps in expected.items():
 obj=B/'objects'/(m.replace('.','/')+'.olean');assert obj.is_file(),m
 artifacts=[]
 for f in [obj,Path(str(obj)+'.server'),Path(str(obj)+'.private'),obj.with_suffix('.ir')]:
  if f.exists():artifacts.append(dict(path=str(f),sha256=sha(f),bytes=f.stat().st_size))
 if m in authority:
  assert artifacts[0]['sha256']==authority[m]['object_sha256'],m
  for cp in authority[m]['companions']:
   assert any(a['sha256']==cp['sha256'] for a in artifacts),cp
 else:
  rs=[json.load(open(f)) for f in B.glob('lean-*/receipt.json') if json.load(open(f)).get('module')==m and json.load(open(f))['exit_status']==0];assert len(rs)==1,m
 rows.append(dict(module=m,imports=deps,artifacts=artifacts,rebuilt=m in p['sources'],source=p['sources'].get(m,{})))
with open('COMBINED-MANIFEST.jsonl','w') as f:
 for r in rows:f.write(json.dumps(r,separators=(',',':'))+'\n')
roots=list(dict.fromkeys(['RPx_Deployed']+p['consumer_imports']));save('SCAN-ROOTS.json',roots)
# Enumerate the exact expected full consumer dependency closure (consumer itself is lead-only).
closure=set()
def visit(m):
 if m in closure:return
 assert m in expected,m
 closure.add(m)
 for d in expected[m]:visit(d)
for m in roots:visit(m)
save('EXPECTED-SCAN-MODULES.json',sorted(closure))
for a,cmd in [(91390,[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','PV_NER_Scan.olean','PV_NER_Scan.lean']),(91391,[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','--run','PV_NER_Scan.lean'])]:
 if Path(f'lean-{a}/receipt.json').exists():
  prior=json.load(open(f'lean-{a}/receipt.json'));assert prior['exit_status']==0 and prior['command']==cmd and prior['source_hashes']['PV_NER_Scan.lean']==sha('PV_NER_Scan.lean')
  print('REUSE FOCUSED CHECK RECEIPT',a,flush=True);continue
 cfg=dict(kind='lean',module='PV_NER_Scan'+('_run' if a==91391 else ''),attempt=f'lean-{a}',sources=['PV_NER_Scan.lean','SCAN-ROOTS.json','EXPECTED-SCAN-MODULES.json'],env=dict(LEAN_PATH=p['LEAN_PATH']),timeout=600,command=cmd,source_revision=json.load(open('AUTHORITY.json'))['workspace_revision'],deps_fingerprint=dict(lean_binary_sha256=lean_binary_sha256,manifest_sha256=sha('COMBINED-MANIFEST.jsonl'),plan_sha256=sha('PLAN.json'),scanner_method='NER_FinalDriverV2 active private checked declarations, types, values, recursor rules and metadata; stable first-occurrence imports; loadExts=false'),expected_time='scanner compilation' if a==91390 else 'combined closure active-kernel import and scan; no elaborator extension caches')
 save(f'attempt-{a}.json',cfg)
 with open(f'admission-{a}.log','w') as log:r=subprocess.run(['python3',str(R/'codex-pv-runjoin-20261026/reservation-existing.py'),f'admission-{a}.json'],stdout=log,stderr=subprocess.STDOUT)
 assert r.returncode==0 and json.load(open(f'admission-{a}.json'))['allowed'] is True,('admission refused; no compiler started',a)
 with open(f'launch-{a}.log','w') as log:r=subprocess.run(['systemd-run','--user','--scope','--quiet',f'--unit=pv-evhc6-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'S2W_run_host.py'),f'attempt-{a}.json'],stdout=log,stderr=subprocess.STDOUT)
 receipt=json.load(open(f'lean-{a}/receipt.json'));print('CHECK',a,receipt['exit_status'],receipt['wall_seconds'],receipt['peak_rss_kib'],flush=True)
 if r.returncode or receipt['exit_status']:
  save('SCAN-STOP.json',dict(attempt=a,receipt=f'lean-{a}/receipt.json',reason='focused check failed; no larger-cap retry'));sys.exit(1)
scan=[json.loads(l) for l in Path('COMBINED-SCAN-ROWS.jsonl').read_text().splitlines()]
assert {r['module'] for r in scan}==closure
assert all(r['imports_match'] and not r['dangling'] for r in scan)
save('SCAN.json',dict(status='coherent',module_count=len(scan),dangling_references=0,dangling_modules=[],imports_all_match=True,declarations=sum(r['declarations'] for r in scan),edges=sum(r['edges'] for r in scan),rows_sha256=sha('COMBINED-SCAN-ROWS.jsonl'),receipt='lean-91391/receipt.json',method='NER_FinalDriverV2 referenceNames + loadedScan; active private kernel; extensions disabled',consumer_body_checked=False,full_consumer_dependencies_scanned=True))
print('SCAN ZERO DANGLING',len(scan),flush=True)
