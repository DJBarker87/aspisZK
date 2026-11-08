"""Offline checks of new session7 evidence; no Lean/raw rerun."""
from pathlib import Path
import subprocess,json,lzma,hashlib,re
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run(['python3',str(L/'session7_abi.py'),'--check'],cwd=R,check=True)
s=json.loads((L/'SESSION7_STATUS.json').read_text());a=json.loads((L/'SESSION7_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION7_RAW_ROOTS.json').read_text())
assert not s['full_task_complete'] and not s['full_source_joint_witness_inhabited']
assert not s['successful_original_history'] and s['checked_local_abi_obstruction']
assert a['exit']==0 and a['roots']==roots['count']==27 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
for m,h in s['source_hashes'].items():
 b=(R/'lean'/(m+'.lean')).read_bytes();assert sha(b)==h
 code=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',code)
for n in range(44910,44917):
 r=json.loads((L/f'receipt-{n}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert int(r['swaps'])==0
 if r['accepted']:assert not any('sorryAx' in t for t in r['axioms_summary_based'])
 else:
  assert n in [44911,44912]
  b=lzma.decompress((L/f'failed-{n}.lean.xz').read_bytes());assert sha(b)==r['source_sha256']
b=lzma.decompress((L/'SESSION7_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION7_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip();g=json.loads(b)
m=json.loads((L/'SESSION7_RAW_GRAPH_MANIFEST.json').read_text());assert len(g)==len(m['roots'])==27
for f in m['files']:assert sha(g[f['name']].encode())==f['sha256']
for c,p in roots['partitions'].items():
 t=(R/'lean'/(p['driver']+'.lean')).read_text();start=t.index('\n  let env ←');assert sha(t[start:].encode())==roots['collector_suffix_sha256']
assert not list(L.rglob('*.olean'))
assert not [p for p in L.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
changed=subprocess.check_output(['git','diff','--name-only',s['base']],cwd=R,text=True).splitlines()
assert all(p.startswith(('lean/PV_LIB_SPEC_','evidence/pv-lib-20261107/lane-SPEC/')) for p in changed)
text=(L/'SESSION7_ABI_BINARY.txt').read_text();assert text.startswith('fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558 ')
for anchor in ['movabs $0x8000000000000000,%r13','mov    $0x30,%edi','mov    $0x8,%esi','movq   $0x1,(%rax)','movq   $0x1,0x8(%rax)','mov    %r14,0x10(%rax)','add    $0x2,%r13','mov    %r13,0x18(%rax)']:assert anchor in text,anchor
archive=json.loads(lzma.decompress((L/'SESSION7_LANEA_SOURCES.json.xz').read_bytes()));pins=json.loads((L/'SESSION7_LANEA_SOURCE_PINS.json').read_text())
for mod,h in pins.items():
 p='lean/'+mod+'.lean';b=subprocess.check_output(['git','show','03c3c72b143:'+p],cwd=R);assert sha(b)==h and archive[p]==b.decode()
print('PASS:27 strict new roots, exact sources/metadata/binary anchors/lane-A pin, caps, retained failures and write boundary; full joint remains open')
