#!/usr/bin/env python3
"""Verify the preserved capped failure and successful finite regressions."""
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
files=bundle('translation.tar.gz','51a671e2e9e04cd32bc0827c1a6d8ae8a97b75b49224fe5b748d2420204cdd5a',35)
reg=bundle('regression.tar.gz','deb46d0921ba585a1f061748bc0e6e22c2cfc0b6f92303d984abc3441c7bcf8c',71)
# Resolve all Git source pins in one blob batch; no proof or dependency replay.
manifests = [json.loads(files[v + '/input/source-pins.json']) for v in ['no-unwrap']]
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
 r=json.loads(files['no-unwrap/runs/'+name+'/receipt.json'])
 assert r['exit_status']==(143 if name=='aeneas-a' else 0)
 assert r['swaps']==0 and r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
 assert r['source_revision']=='b330ade02e82770977de48471ee0d0b886c0e796'
stop=json.loads(files['no-unwrap/runs/aeneas-a/operator-stop.json']);assert stop['signal']=='SIGTERM'
assert json.loads(files['private-geometry-tool.json'])['binary_sha256']=='849dc33c427441499c7364d3d7c6426e2ef48be7f9859ab8456efc859394ebd0'
with tempfile.TemporaryDirectory() as temp:
 p=Path(temp);(p/'adapter.py').write_bytes(files['j1-rename-enum-constructors.py']);(p/'in.llbc').write_bytes(files['no-unwrap/extraction-a/TerminalDecoder.llbc'])
 subprocess.run(['python3',str(p/'adapter.py'),str(p/'in.llbc'),str(p/'out.llbc'),str(p/'report.json')],check=True,stdout=subprocess.PIPE)
 assert (p/'out.llbc').read_bytes()==files['no-unwrap/extraction-a/TerminalDecoder-renamed.llbc']
 r=json.loads((p/'report.json').read_text());assert len(r['changes'])==4 and r['restored_complete_json_equals_input']
trace=files['no-unwrap/runs/trace-a/stdout.log']
assert len(trace)==66622110 and trace.endswith(b'complete 20720\n') and sha(trace)=='628a3418096f93d769955ff18e7ac2f4e8fcb25b659b66aac3360204ad94efff'
assert json.loads(files['no-unwrap/native-comparison.json'])['byte_identical']
for n,d in reg.items():
 if n.endswith('/receipt.json'):
  r=json.loads(d);assert r['exit']==0 and r['swap_current_bytes']==0
  assert r['limits']=={'memory.high':'8589934592','memory.max':'10737418240','memory.swap.max':'0'}
s=json.loads(reg['SUMMARY.json']);c=s['comparison'];assert c['delta']=={'stage1':1414,'stage2':533,'sum':1947}
for k in ['both_admitted_pairs_accepted','initial_images_equal','checkpoint_equal','asr8_equal']:assert c[k]
assert not c['setup_cu_included']
for kind,folder in [('baseline','before-sbf'),('candidate','after-sbf-fresh-artifacts')]:assert sha(reg[folder+'/aspis_r1_cost_probe_program.so'])==s[kind+'_elf_sha256']
assert b'1 passed; 0 failed' in reg['runs/after-counter/build.log']
print(f'PASS:106 archive entries; {len(requests)} Git source pins; extraction stop143 retained; native20720 equality/counter/SBF/CU+1947. This candidate is NOT extraction-closed.')
