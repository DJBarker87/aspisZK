from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).parent
roots=json.loads((E/'AUDIT_ROOTS.json').read_text())
audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert audit['strict_pass'] and audit['receipt']['accepted'] and audit['receipt']['exit']=='0'
assert audit['unresolved']==audit['summary_mismatches']==0
assert len(audit['roots'])==10 and set(roots['roots'])=={r['root'] for r in audit['roots']}
for r in audit['roots']:
 assert r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
for s in json.loads((E/'SUPPORT.json').read_text()):
 assert hashlib.sha256(Path(s['source']).read_bytes()).hexdigest()==s['source_sha256']
for p in E.glob('receipt-*.json'):
 r=json.loads(p.read_text()); n=r['attempt']
 assert 55674<=n<=55689 or n==55691
 assert r['command'][r['command'].index('MemoryHigh=6G')]=='MemoryHigh=6G'
 assert 'MemoryMax=8G' in r['command'] and 'MemorySwapMax=0' in r['command'] and 'TasksMax=64' in r['command']
 if not r['accepted']:
  assert (E/f'failed-{n}.lean.xz').exists()
  assert hashlib.sha256(lzma.decompress((E/f'failed-{n}.lean.xz').read_bytes())).hexdigest()==r['source_sha256']
manifest=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text())
assert hashlib.sha256((E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes()).hexdigest()==manifest['archive_sha256']
assert hashlib.sha256(lzma.decompress((E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes())).hexdigest()==manifest['uncompressed_sha256']
changed=subprocess.check_output(['git','diff','--name-only','5894298db30'],text=True).splitlines()
assert all(p.startswith('evidence/pv-lib-20261107/lane-A/') or p.startswith('lean/PV_LIB_A_') for p in changed)
print('PASS:10 strict support roots; all four LaneAJoins18 targets remain OPEN')
