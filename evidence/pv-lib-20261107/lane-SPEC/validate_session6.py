"""Offline verification of retained session6 inputs/results; invokes no Lean."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent
R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
status=json.loads((L/'SESSION6_STATUS.json').read_text())
roots=json.loads((L/'SESSION6_RAW_ROOTS.json').read_text())
audit=json.loads((L/'SESSION6_RAW_AUDIT.json').read_text())
assert audit['exit']==0 and audit['roots']==roots['count']==115
assert audit['all_equal'] and audit['standard_axioms_only'] and audit['unresolved']==0
assert not audit['rerun'] and not status['full_task_complete']
assert not status['full_source_joint_witness_inhabited']
for module,expected in status['source_hashes'].items():
 p=R/'lean'/(module+'.lean')
 assert sha(p.read_bytes())==expected,module
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)),module
 records=[json.loads(f.read_text()) for f in L.glob('receipt-*.json')]
 accepted=[r for r in records if r.get('target')==module and r.get('accepted')]
 assert any(r['source_sha256']==expected for r in accepted),module
for r in status['attempts']:
 assert int(r['swaps'])==0
 actual=json.loads((L/f"receipt-{r['attempt']}.json").read_text())
 assert actual['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert actual['exit']==r['exit']
 if actual['accepted']:assert all('sorryAx' not in line for line in actual['axioms_summary_based'])
archive=lzma.decompress((L/'SESSION6_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
assert sha(archive)==(L/'SESSION6_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
graphs=json.loads(archive)
manifest=json.loads((L/'SESSION6_RAW_GRAPH_MANIFEST.json').read_text())
assert len(graphs)==len(manifest['roots'])==115
for item in manifest['files']:assert sha(graphs[item['name']].encode())==item['sha256']
changed=subprocess.check_output(['git','diff','--name-only',status['base']],cwd=R,text=True).splitlines()
assert all(p.startswith(('lean/PV_LIB_SPEC_','evidence/pv-lib-20261107/lane-SPEC/')) for p in changed)
assert not list(L.rglob('*.olean'))
assert not [p for p in L.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
print('PASS: exact accepted sources,115 strict roots,standard axioms,caps,archive and write boundary; full joint remains unestablished')
