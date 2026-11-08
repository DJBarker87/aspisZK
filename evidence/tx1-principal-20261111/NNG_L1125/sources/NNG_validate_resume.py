"""Validate only this continuation's receipts, source snapshots and new roots."""
from pathlib import Path
import json,hashlib,re,lzma,sys
B=Path.cwd();given=json.loads((B/'NNG_RESUME_VALIDATION_INPUTS.json').read_text());allowed={'propext','Classical.choice','Quot.sound'}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
rows=[];snapshots=0;heartbeats=[]
for a,admission in sorted(given['admissions'].items()):
 r=json.loads((B/a/'receipt.json').read_text());assert r['attempt']==a
 assert r['limits']==limits,(a,r['limits']);assert int(r['swaps'])==0
 assert r['source_revision'] and r['wall_seconds']>=0 and int(r['peak_rss_kib'])>0
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 host=json.loads((B/(a+'-reservation.json')).read_text());assert host==admission['reservation'],a
 assert given['final_disk'][a]>=40_000_000_000 and given['final_share'][a]<6
 for name,sha in r['source_hashes'].items():
  source=B/a/'sources'/name;assert source.is_file(),(a,source)
  assert hashlib.sha256(source.read_bytes()).hexdigest()==sha,(a,name);snapshots+=1
 if r['kind']=='lean':assert '-M7000' in r['command'] and '-j1' in r['command']
 stdout=(B/a/'stdout.log').read_text()
 assert r['exit_status'] not in [124,137,-9],a
 assert 'excessive memory consumption' not in stdout.lower() and 'memory limit exceeded' not in stdout.lower(),a
 if 'maximum number of heartbeats' in stdout:heartbeats.append(a)
 rows.append({k:r[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
for module,item in given['selected'].items():
 r=json.loads((B/item['attempt']/'receipt.json').read_text());assert r['exit_status']==0
 path='NNG_generated/'+item['source'];assert r['source_hashes'][path]==item['sha256']
 assert hashlib.sha256((B/path).read_bytes()).hexdigest()==item['sha256'],module
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  m=re.search(r'depends on axioms: \[([^]]*)\]',line)
  if m:assert set(filter(None,(x.strip() for x in m[1].split(','))))<=allowed,line
retained=json.loads((B/'NNG_RESUME_RETAINED_OBJECTS.json').read_text())
for module in retained['modules']:
 for f in module['files']:
  p=Path(f['path']);assert p.is_file() and p.stat().st_size==f['bytes']
  assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],p
manifest=json.loads((B/'NNG_Resume_AUDIT_ROOTS.json').read_text());expected=[r for g in manifest['groups']for r in g];results=[];pairs=0
for i,group in enumerate(manifest['groups']):
 mode='proof'+str(i);folder=B/'NNG_Resume_audit'/mode;raw=json.loads((folder/(mode+'.json')).read_text())
 assert raw['exit_status']==0 and {r['root']for r in raw['results']}==set(group)
 for r in raw['results']:
  assert r['equal'] and set(r['collect_axioms'])==set(r['walked_axioms'])<=allowed,r
  results.append(r)
 for p in folder.glob('*.xz'):
  digest=hashlib.sha256()
  with lzma.open(p,'rb')as source:
   for block in iter(lambda:source.read(1024*1024),b''):digest.update(block)
  assert digest.hexdigest()==Path(str(p)[:-3]+'.sha256').read_text().strip(),p;pairs+=1
assert len(results)==len(expected)==len(set(expected))
assert set(heartbeats)=={'NNG_L1034','NNG_L1098'},heartbeats
formal=sum(r['kind']in['lean','link','audit']for r in rows);assert formal<=300
result=dict(status='PASS',validation_scope=sys.argv[1],actual_completed_scopes=len(rows),fresh_lean_link_audit_scopes=formal,baseline_lean_link_audit_scopes=830,lifetime_lean_link_audit_scopes=830+formal,fresh_allowance=300,remaining_formal_scopes=300-formal,source_snapshots=snapshots,source_matched_modules=len(given['selected']),retained_modules=len(retained['modules']),audited_roots=len(results),verified_archive_sha_pairs=pairs,heartbeats_retired_and_split=heartbeats,wall_timeouts_or_OOM=0,swap=0,standard_axioms=sorted(allowed),unresolved_other_submissions=given['unresolved_other_submissions'],frozen_source_check=given['frozen_source_check'],scope_rows=rows)
assert not result['unresolved_other_submissions']
(B/'NNG_RESUME_FINAL_VALIDATION.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:result[k]for k in ['status','fresh_lean_link_audit_scopes','remaining_formal_scopes','source_snapshots','source_matched_modules','retained_modules','audited_roots','verified_archive_sha_pairs','heartbeats_retired_and_split']}))
