#!/usr/bin/env python3
"""Verify the focused theorem's retained sources/receipts/objects without replay."""
from pathlib import Path
import hashlib,json,tarfile
base=Path(__file__).resolve().parent
sha=lambda data:hashlib.sha256(data).hexdigest()
key=lambda value:sha(json.dumps(value,sort_keys=True).encode())
def load(path):
    with tarfile.open(path,'r:gz') as tf:return {m.name:tf.extractfile(m).read() for m in tf if m.isfile()}
m=json.loads((base/'manifest.json').read_text());archive=base/m['archive']
assert sha(archive.read_bytes())==m['archive_sha256'];files=load(archive)
assert len(files)==m['archive_entries']
for line in files['SHA256SUMS'].decode().splitlines():
    digest,name=line.split('  ',1);assert sha(files[name])==digest,name
name=m['target'];source='sources/'+name+'.lean'
assert sha(files[source])==m['source_sha256']
assert (base.parent.parent/'lean'/(name+'.lean')).read_bytes()==files[source]
r=json.loads(files[m['receipt']]);assert r['exit_status']==0 and r['axioms']['passed']
assert r['key']['source_sha256']==m['source_sha256']
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
for suffix,obj in r['objects'].items():assert sha(files['objects/'+name+suffix])==obj['sha256']
closed_path=base.parent/'terminal-closed-cone-432-20261016/checked-sources-receipts-objects.tar.gz'
assert sha(closed_path.read_bytes())==m['closed_bundle_sha256'];closed=load(closed_path)
for dep in ['AspisR1TerminalValidator.Types','AspisR1TerminalValidator.FunsExternal','AspisR1TerminalValidator.Funs','ExtractedTerminalEquality']:
    rp='successful-targets/'+dep+'.json';dr=json.loads(files[rp])
    assert files[rp]==closed[rp]
    assert files['sources/'+dep.replace('.','/')+'.lean']==closed['sources/'+dep.replace('.','/')+'.lean']
    for suffix,obj in dr['objects'].items():assert sha(closed['objects/'+dep.replace('.','/')+suffix])==obj['sha256']
dep=json.loads(files['successful-targets/ExtractedTerminalEquality.json'])
assert r['key']['imports']['ExtractedTerminalEquality']=={'receipt_key':key(dep['key']),'objects':dep['objects']}
assert r['key']['runtime']==dep['key']['runtime'] and r['key']['options']==['-j1','-M0']
print(f"PASS: {len(files)} entries; actual proof/source/object; exact four checked predecessors; one standard-only theorem audit")
