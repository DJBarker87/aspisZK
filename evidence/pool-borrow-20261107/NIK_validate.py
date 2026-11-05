"""Fail-closed evidence validation; does not promote model work to native credit."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads((E/p).read_text())
required=['NIK_CENSUS.json','NIK_DISCIPLINE.md','NIK_OPEN_SITES.md','NIK_STUBS.md','NIK_Invariant.lean','NIK_CLOSED.json','NIK_LEDGER_DELTA.json','NIK_AUDIT.json','NIK_COMBINED_IMPORT.lean','NIK_FAILING_STEP.md','NIK_HANDOFF.md','NIK_REMAINING.md','NIK_ATTEMPTS.jsonl']
assert all((E/n).is_file() for n in required)
census=read('NIK_CENSUS.json');frozen=census['frozen_revision']
for pin in census['source_pins']:
 raw=subprocess.check_output(['git','show',frozen+':'+pin['path']],cwd=R)
 assert sha(raw)==pin['sha256'] and len(raw)==pin['bytes']
assert census['counts']['unresolved']==0 and len(census['mir_calls'])==2353
assert len(read('NIK_ALL_ACCESSORS.json'))==21
assert sum(any(c['category']=='exclusive' for c in f['calls']) for f in census['functions'] if f['mir_headers'])==13
for n in ['NIK_M001_artifacts/NIK_pool.mir','NIK_CLOSURE_PINS.json','NIK_SDK_INPUT.json']:
 raw=lzma.decompress((E/(n+'.xz')).read_bytes());assert sha(raw)==(E/(n+'.sha256')).read_text().strip()
for p in read('NIK_SDK_ARCHIVE_CHECK.json'):
 assert p['archive_matches_frozen'] and all(c['matches'] for c in p['checks'])
assert read('NIK_M001_artifacts/lock-check.json')['unchanged']
attempts=[json.loads(l) for l in (E/'NIK_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in attempts})==len(attempts)
assert not [r for r in attempts if r['kind']=='kani']
assert sum(r['kind']=='extract' for r in attempts)==1
assert sum(r['kind']=='mir' for r in attempts)==1
assert len([r for r in attempts if r['attempt'].startswith('NIK_L')])<=60
for r in attempts:
 ad=read(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
allowed={'propext','Classical.choice','Quot.sound'}
for mod,num in [('NIK_Counter',7),('NIK_Footprint',8),('NIK_Headroom',6),('NIK_Invariant',11),('NIK_COMBINED_IMPORT',12)]:
 a=f'NIK_L{num:03}';r=read(a+'/receipt.json');assert r['exit_status']==0
 source=(E/(mod+'.lean')).read_bytes();assert r['source_hashes']['NIK_generated/'+mod+'.lean']==sha(source)
 assert not re.search(rb'\b(?:sorry|admit|axiom|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',source)
 for theorem in re.findall(rb'^theorem\s+(\w+)',source,re.M):
  name=mod+'.'+theorem.decode();assert any("'"+name+"'" in line for line in r['print_axioms'])
 for line in r['print_axioms']:
  m=re.search(r'axioms: \[(.*?)\]',line)
  if m:assert set(x.strip() for x in m[1].split(',') if x.strip())<=allowed
raw=read('NIK_audit/batch0/proof0.json');roots=read('NIK_AUDIT_ROOTS.json')['groups'][0]
assert raw['exit_status']==0 and {x['root'] for x in raw['results']}==set(roots)
assert all(x['equal'] and set(x['walked_axioms'])<=allowed for x in raw['results'])
fixture=read('NIK_audit/fixtures/fixtures.json');baseline=json.loads((E.parent/'pool-b4-20261107/NIE_audit/fixtures/fixtures.json').read_text())
project=lambda d:[{k:r[k] for k in ['root','equal','collect_axioms','walked_axioms']} for r in d['results']]
assert fixture['exit_status']==0 and len(fixture['results'])==8 and project(fixture)==project(baseline)
scan=[json.loads(l) for l in (E/'NIK_LOADED_scan.jsonl').read_text().splitlines()]
assert read('NIK_L019/receipt.json')['exit_status']==0
assert all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in scan)
assert not read('NIK_CLOSED.json')['closed_pool_consumer_rows']
assert not read('NIK_CLOSED.json')['native_per_function_certificates']
assert not read('NIK_LEDGER_DELTA.json')['pool_consumer_rows']
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
subprocess.run(['git','diff','--check'],cwd=R,check=True,capture_output=True)
report=dict(status='PASS_PARTIAL_EVIDENCE_ONLY',native_invariant_established=False,closed_pool_delta=0,attempts=len(attempts),roots=len(roots),scan_modules=len(scan),source_files=len(census['source_pins']),native_certificates=0)
(E/'NIK_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n')
print('NIK validation PASS for partial evidence; no native invariant or Pool row credit')
