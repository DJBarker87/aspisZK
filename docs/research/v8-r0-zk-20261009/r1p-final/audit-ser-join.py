#!/usr/bin/env python3
"""Freeze diagnostic evidence, without claiming serialization refinement."""
import hashlib, json, pathlib, re, shlex, subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
BASE='542fe958f'
module='R1Z/SerJoinOrderObstruction'
src=HERE.parent/'lean'/(module+'.lean')
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((HERE/'ser-join-attempts-8500-8599.jsonl').read_text().strip())
assert r['attempt']==8500 and r['exit']==0 and r['swaps']=='0'
assert r['source_sha256']==digest(src)
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+max(RecDepth|Heartbeats)',src.read_text())
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",r['output'])
assert len(reports)==5
for name, axioms in reports:
    assert set(axioms.split(', ')) <= {'propext','Classical.choice','Quot.sound'}
j='/home/dombarker/project-offloads/aspis-joint-20261019'
branch='/home/dombarker/project-offloads/codex-cx-ser-join-20261021'
paths=[f'{j}/sources/{module}.lean',f'{j}/objects/{module}.olean']
paths += [line.split(None,1)[1] for line in r['dependency_objects']]
paths += [f'{branch}/source/crates/aspis-core/src/r0_transcript.rs',f'{branch}/source/crates/aspis-core/build.rs',f'{branch}/source/probe/src/main.rs']
script='''import pathlib,hashlib,json
print(json.dumps({s:dict(sha256=hashlib.sha256(pathlib.Path(s).read_bytes()).hexdigest(),size=pathlib.Path(s).stat().st_size) for s in PATHS}))
'''.replace('PATHS',repr(paths))
host=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],text=True,timeout=60))
assert host[paths[0]]['sha256']==digest(src)
for line in r['dependency_objects']:
    sha,path=line.split(None,1)
    assert host[path]['sha256']==sha
assert host[f'{branch}/source/crates/aspis-core/src/r0_transcript.rs']['sha256']==digest(ROOT/'crates/aspis-core/src/r0_transcript.rs')
assert host[f'{branch}/source/crates/aspis-core/build.rs']['sha256']==digest(ROOT/'crates/aspis-core/build.rs')
assert host[f'{branch}/source/probe/src/main.rs']['sha256']==digest(HERE/'ser-join-sampler-probe.rs')
native=json.loads((HERE/'ser-join-sampler-evidence.json').read_text())
assert native['exit']==0 and native['probe_sha256']==digest(HERE/'ser-join-sampler-probe.rs')
w=json.loads(native['stdout'])
assert set(w['first'])==set(w['crossed']) and w['first_batch']!=w['crossed_batch']
for entry in native['source_tree']:
    assert digest(ROOT/entry['path'])==entry['sha256']
endpoint=HERE.parent/'lean/R1Z/ProverCommitAdmittedEndpoint.lean'
sig=endpoint.read_text().split('theorem privacy_headline_admitted',1)[1].split(' := by',1)[0]
assert 'RustSerializationJoin' not in sig
changed=subprocess.check_output(['git','diff','--name-status',BASE],cwd=ROOT,text=True).splitlines()
assert all(line.startswith('A\t') for line in changed),changed
assert all(line.split('\t',1)[1].startswith('docs/research/v8-r0-zk-20261009/') for line in changed)
source_paths=['crates/aspis-core/src/r0_transcript.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/transcript.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/compact.rs','docs/research/v8-r0-zk-20261009/lean/R0Z/HonestView.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PhaseWireLog2Bin.lean',str(endpoint.relative_to(ROOT))]
audit=dict(status='diagnostic evidence verified; target not yet established',base=BASE,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),module=module,attempt=8500,source_sha256=digest(src),deps_fingerprint=r['deps_fingerprint'],exit=0,wall=r['wall'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axioms=reports,host_objects_and_sources=host,source_pins={p:digest(ROOT/p) for p in source_paths},all_tracked_changes_additions=True,shipped_files_changed=False,fresh_elf_rebuild=False,full_manifest_replay=False,kani_certificate=False,aeneas_extraction=False,RustSerializationJoin_discharged=False,endpoint_binder_removed=False,remaining='Preserve ordered q22 and transport privacy experiment before source serializer refinement')
(HERE/'ser-join-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({k:audit[k] for k in ['status','source_revision','attempt','exit','wall','peak_rss_kib','swaps']}))
