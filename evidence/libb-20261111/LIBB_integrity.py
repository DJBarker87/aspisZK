"""Read-only receipt/source/axiom integrity gate; --final requires full budget/coverage."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess,sys
E=Path(__file__).resolve().parent;final='--final'in sys.argv
allowed={'propext','Classical.choice','Quot.sound'}
rows=[json.loads(p.read_text()) for p in sorted(E.glob('LIBB_L[0-9][0-9][0-9]/receipt.json'))]
assert len(rows)<=300
if final:assert len(rows)==300
shares={}
for s in (E/'LIBB_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(s)
 if r.get('event')=='share_check':shares.setdefault(r['attempt'],[]).append(r['host']['count'])
expected_limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
aeneas={};selected={};sources=0
for r in rows:
 a=r['attempt'];assert r['limits']==expected_limits,(a,r['limits'])
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True,a
 diskfiles=sorted(E.glob(a+'-disk-*.json'),key=lambda p:int(p.stem.rsplit('-',1)[1]))
 assert json.loads(diskfiles[-1].read_text())['free']>=40_000_000_000,a
 assert shares[a]and shares[a][-1]<6,a
 assert r['exit_status']not in [124,137,-9],('Timeout/kill audit required',a)
 for rel,sha in r['source_hashes'].items():
  p=E/a/'sources'/rel
  assert p.exists(),p
  assert hashlib.sha256(p.read_bytes()).hexdigest()==sha,(a,rel)
  sources+=1
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx'not in line,line
   found=re.search(r'depends on axioms: \[([^]]*)\]',line)
   if found:assert {x.strip()for x in found[1].split(',')if x.strip()}<=allowed,line
 for path,pin in r['deps_fingerprint']['selected_objects'].items():
  selected.setdefault(path,set()).add(pin['sha256'])
  if '/Aeneas/'in path or '/AeneasMeta/'in path or path.endswith('/Aeneas.olean')or path.endswith('/AeneasMeta.olean'):
   aeneas.setdefault(path,set()).add(pin['sha256'])
assert all(len(v)==1 for v in aeneas.values()),'Aeneas object drift'
idx=json.loads((E/'LIBB_AUDIT_INDEX.json').read_text());groups=json.loads((E/'LIBB_AUDIT_ROOTS.json').read_text())['groups'];audited=set()
for p in (E/'LIBB_audit').glob('proof*/proof*.json'):
 j=json.loads(p.read_text());g=int(j['target'].removeprefix('proof'))
 assert j['exit_status']==0
 assert [x['root']for x in j['results']]==groups[g]
 for r in j['results']:
  assert set(r['walked_axioms'])<=allowed,r
  assert r['root']not in audited,r['root'];audited.add(r['root'])
for r in idx:
 assert hashlib.sha256((E/(r['module']+'.lean')).read_bytes()).hexdigest()==r['source_sha256']
 if final:assert r['root']in audited,r['root']
compressed=0
for p in E.glob('LIBB_NEP*_REACHABLE.txt.xz'):
 h=hashlib.sha256()
 with lzma.open(p,'rb')as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 assert h.hexdigest()==p.with_suffix('.sha256').read_text().strip(),p
 compressed+=1
export=json.loads((E/'LIBB_EXPORT.json').read_text())
for x in export['objects']:
 if x['path']in selected:assert selected[x['path']]=={x['sha256']}
 # Original own object and retained export have identical relative names.
 original=x['path'].replace('/LIBB_exports_20261111/','/LIBB_objects/')
 if original in selected:assert selected[original]=={x['sha256']},original
oversize=[str(p.relative_to(E))for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
assert not oversize,oversize
base='198f29a487ce5a72061c3ff09063c8cf176e7f11'
changed=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs','Cargo.lock'],text=True).splitlines();assert not changed,changed
allchanges=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines();assert all(p.startswith('evidence/libb-20261111/')for p in allchanges)
answer=dict(final=final,scopes=len(rows),source_snapshots_checked=sources,own_roots=len(idx),raw_roots_checked=len(audited),compressed_raw_hashes_checked=compressed,aeneas_objects_stable=len(aeneas),retained_own_objects=len(export['objects']),oversize=[],shipped_source_changes=[],foreign_changes=[],caps_exact=True,admissions_exact=True,disk_checks_pass=True,share_checks_pass=True,unchanged_timeout_or_memory_kill_replay=False,target_established=False,row_credit_claimed=False)
(E/'LIBB_INTEGRITY.json').write_text(json.dumps(answer,indent=2)+'\n')
(E/'LIBB_AENEAS_PINS.json').write_text(json.dumps({k:next(iter(v))for k,v in sorted(aeneas.items())},indent=1)+'\n')
print(json.dumps(answer))
