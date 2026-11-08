"""Offline evidence validation. Does not rerun Lean or the strict audit."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION8_STATUS.json').read_text());a=json.loads((L/'SESSION8_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION8_RAW_ROOTS.json').read_text())
assert not s['full_task_complete'] and not s['full_source_joint_witness_inhabited'] and not s['successful_original_history']
assert not s['full_joint_contradiction_proved'] and s['local_allBridged_applied'] and not s['local_callback_destination_registered']
assert a['exit']==0 and a['roots']==roots['count']==81 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
failed=[];accepted=[]
for n in range(44917,44937):
 r=json.loads((L/f'receipt-{n}.json').read_text());ad=json.loads((L/f'admission-{n}.json').read_text())
 assert ad['allowed'] is True
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert int(r['swaps'])==0
 if r['accepted']:
  accepted.append(n)
  assert not any('sorryAx' in t for t in r['axioms_summary_based'])
  assert sha((R/'lean'/(r['target']+'.lean')).read_bytes())==r['source_sha256']
 else:
  failed.append(n)
  b=lzma.decompress((L/f'failed-{n}.lean.xz').read_bytes());assert sha(b)==r['source_sha256']
assert accepted==s['accepted_focused'] and failed==s['failed_focused']
for m,h in s['source_hashes'].items():
 b=(R/'lean'/(m+'.lean')).read_bytes();assert sha(b)==h
 code=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',code)
b=lzma.decompress((L/'SESSION8_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION8_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip();g=json.loads(b)
m=json.loads((L/'SESSION8_RAW_GRAPH_MANIFEST.json').read_text());assert len(g)==len(m['roots'])==81
for f in m['files']:assert sha(g[f['name']].encode())==f['sha256']
for c,p in roots['partitions'].items():
 t=(R/'lean'/(p['driver']+'.lean')).read_text();assert sha(t.encode())==p['source_sha256'];start=t.index('\n  let env ←');assert sha(t[start:].encode())==roots['collector_suffix_sha256']
assert not list(L.rglob('*.olean'))
assert not [p for p in L.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
changed=subprocess.check_output(['git','diff','--name-only',s['base']],cwd=R,text=True).splitlines()
assert all(p.startswith(('lean/PV_LIB_SPEC_','evidence/pv-lib-20261107/lane-SPEC/')) for p in changed)
for file in ['SESSION8_ABI_SCOPE.txt','SESSION8_ABI_CALLBACK_INIT.txt']:
 assert (L/file).read_text().startswith(s['adopted_elf_sha256']+' ')
for r in m['roots']:assert set(r['walked_axioms']) <= {'propext','Classical.choice','Quot.sound'}
print('PASS:81 strict new roots;9 focused passes,11 changed-before-retry errors;exact sources/caps/evidence/write boundary;full joint remains OPEN')
