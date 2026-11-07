"""Check retained evidence and scope; never runs Lean or a raw audit."""
import hashlib,json,lzma,re,subprocess
from pathlib import Path
P=Path(__file__).resolve().parent
repo=P.parents[2]
def sha(b):return hashlib.sha256(b).hexdigest()
validation=json.loads((P/'SESSION4_VALIDATION.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
for a in [49732,49733,49734,49735,49736]:
 r=json.loads((P/f'receipt-{a}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert json.loads((P/f'admission-{a}.json').read_text())['allowed'] is True
 if r['accepted']:
  assert sha((repo/'lean'/(r['target']+'.lean')).read_bytes())==r['source_sha256']
  assert all('sorryAx' not in l for l in r['axioms_summary_based'])
 else:
  assert sha(lzma.decompress((P/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
assert len({json.loads((P/f'receipt-{a}.json').read_text())['source_sha256'] for a in [49732,49733,49734,49735]})==4
roots=json.loads((P/'SESSION4_AUDIT_ROOTS.json').read_text())['roots']
man=json.loads((P/'SESSION4_RAW_GRAPH_MANIFEST.json').read_text())
assert len(roots)==7 and sorted(roots)==sorted(r['root'] for r in man['roots'])
archive=lzma.decompress((P/'SESSION4_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
assert sha(archive)==(P/'SESSION4_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
graphs=json.loads(archive)
for v in man['files']:
 assert sha(graphs[v['name']].encode())==v['sha256']
 assert len(graphs[v['name']].encode())==v['bytes']
for r in man['roots']:
 assert r['equal'] and set(r['walked_axioms']) <= allowed
 assert r['summary_axioms']==r['walked_axioms']
audit=json.loads((P/'receipt-49794.json').read_text())
assert audit['exit']==0 and audit['accepted']
assert json.loads((P/'admission-49794.json').read_text())['allowed'] is True
new=(repo/'lean/PV_LIB_SPEC_RawAuditSession4.lean').read_text()
old=(repo/'lean/PV_LIB_SPEC_RawAuditFinal3.lean').read_text()
assert new[new.index('  let env ←'):]==old[old.index('  let env ←'):]
index=json.loads((P/'CONTRACT_INDEX.json').read_text())
assert len(index['session4_scope']['active_rows'])==18
assert index['session4_scope']['full_frozen_thread_contracts']==0
assert index['session4_scope']['ownInit_joint_witnesses']==0
changed=subprocess.check_output(['git','diff','a84dc05c68e','--name-only'],cwd=repo,text=True).splitlines()
assert all(f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f in [
 'lean/PV_LIB_SPEC_F361ArcMachineGap.lean','lean/PV_LIB_SPEC_RawAuditSession4.lean'] for f in changed)
for f in [repo/'lean/PV_LIB_SPEC_F361ArcMachineGap.lean',repo/'lean/PV_LIB_SPEC_RawAuditSession4.lean']:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',f.read_text())
assert not any(f.stat().st_size>20*1024*1024 for f in P.rglob('*') if f.is_file())
print('PASS: retained sources, receipts, 7 strict raw graphs, unchanged walker, D983 scope; full contracts0/18, OwnInit witness0/1')
