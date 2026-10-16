#!/usr/bin/env python3
"""Verify the final helper extraction and finite regressions."""
from pathlib import Path
import hashlib,io,json,subprocess,tarfile,tempfile
base=Path(__file__).resolve().parent
sha=lambda data:hashlib.sha256(data).hexdigest()
def bundle(name,digest,count):
 p=base/name;assert sha(p.read_bytes())==digest
 with tarfile.open(p) as t:
  members=t.getmembers();assert len(members)==count and len({m.name for m in members})==count
  assert all(m.isfile() and not m.name.endswith('.key') and not m.name.endswith('-keypair.json') for m in members)
  data={m.name:t.extractfile(m).read() for m in members}
 for n,pin in json.loads(data['archive-members.json']).items():assert len(data[n])==pin['bytes'] and sha(data[n])==pin['sha256']
 return data
files=bundle('translation.tar.gz','ffbef9310466fc444eb478cd1b7fbe33f96cbeabcbbf942990f784d0874bd3ec',38)
reg=bundle('regression.tar.gz','33bc4e850c66032bc2b7dee60881dbf9cde1fbd2c3de5b893c069b4c67378643',71)
# Resolve all Git source pins in one blob batch; no proof or dependency replay.
manifests = [json.loads(files[v + '/input/source-pins.json']) for v in ['copy-helper']]
requests = [(j['source_revision'], p, h) for j in manifests for p, h in j['kit_files'].items()]
requests += [(j['revision'], p, h) for j in [json.loads(reg[k + '-manifest.json']) for k in ['before', 'after']] for p, h in j['files'].items()]
trees = {}
for rev, _, _ in requests:
    if rev in trees:
        continue
    raw = subprocess.check_output(['git', 'ls-tree', '--full-tree', '-rz', rev], cwd=base)
    trees[rev] = {entry.split(b'\t', 1)[1].decode(): entry.split(b'\t', 1)[0].split()[2].decode()
                  for entry in raw.split(b'\0') if entry}
oids = sorted({trees[rev][p] for rev, p, _ in requests})
raw = subprocess.run(['git', 'cat-file', '--batch'], input=('\n'.join(oids) + '\n').encode(),
                     stdout=subprocess.PIPE, check=True, cwd=base).stdout
stream = io.BytesIO(raw); hashes = {}
for oid in oids:
    header = stream.readline().split(); assert header[0].decode() == oid and header[1] == b'blob'
    data = stream.read(int(header[2])); assert stream.read(1) == b'\n'; hashes[oid] = sha(data)
assert not stream.read()
for rev, path, digest in requests:
    assert hashes[trees[rev][path]] == digest, (rev, path)

for name in ['charon-a','aeneas-a','build-a','trace-a']:
 r=json.loads(files['copy-helper/runs/'+name+'/receipt.json'])
 assert r['exit_status']==0
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
 assert r['source_revision']=='0626294e34632812accf4cb14704f027368ea871'
assert b'Error' not in files['copy-helper/runs/aeneas-a/stdout.log']
assert json.loads(files['private-geometry-tool.json'])['binary_sha256']=='849dc33c427441499c7364d3d7c6426e2ef48be7f9859ab8456efc859394ebd0'
with tempfile.TemporaryDirectory() as temp:
 p=Path(temp);(p/'adapter.py').write_bytes(files['j1-rename-enum-constructors.py']);(p/'in.llbc').write_bytes(files['copy-helper/extraction-a/TerminalDecoder.llbc'])
 subprocess.run(['python3',str(p/'adapter.py'),str(p/'in.llbc'),str(p/'out.llbc'),str(p/'report.json')],check=True,stdout=subprocess.PIPE)
 assert (p/'out.llbc').read_bytes()==files['copy-helper/extraction-a/TerminalDecoder-renamed.llbc']
 r=json.loads((p/'report.json').read_text());assert len(r['changes'])==4 and r['restored_complete_json_equals_input']
trace=files['copy-helper/runs/trace-a/stdout.log']
assert len(trace)==66622110 and trace.endswith(b'complete 20720\n') and sha(trace)=='628a3418096f93d769955ff18e7ac2f4e8fcb25b659b66aac3360204ad94efff'
assert json.loads(files['copy-helper/native-comparison.json'])['byte_identical']
for n,d in reg.items():
 if n.endswith('/receipt.json'):
  r=json.loads(d);assert r['exit']==0 and r['swap_current_bytes']==0
  assert r['limits']=={'memory.high':'8589934592','memory.max':'10737418240','memory.swap.max':'0'}
s=json.loads(reg['SUMMARY.json']);c=s['comparison'];assert c['delta']=={'stage1':1344,'stage2':502,'sum':1846}
for k in ['both_admitted_pairs_accepted','initial_images_equal','checkpoint_equal','asr8_equal']:assert c[k]
assert not c['setup_cu_included']
for kind,folder in [('baseline','before-sbf'),('candidate','after-sbf-fresh-artifacts')]:assert sha(reg[folder+'/aspis_r1_cost_probe_program.so'])==s[kind+'_elf_sha256']
assert b'1 passed; 0 failed' in reg['runs/after-counter/build.log']
print(f'PASS:109 entries; {len(requests)} Git source pins; actual extraction success; native20720 byte equality/counter/SBF/CU+1846. Actual Lean declaration audit is separate.')
