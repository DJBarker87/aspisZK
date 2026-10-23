#!/usr/bin/env python3
"""Read-only audit of synced build sources and full pinned ELF bytes."""
import hashlib,json,subprocess
from pathlib import Path
R=Path(__file__).resolve().parent.parent
prefixes=('crates/','programs/','audit/','xtask/','docs/research/v8-r0-zk-20261009/z4/','docs/research/v8-r0-zk-20261009/c3/','docs/research/v8-r0-zk-20261009/refine/')
files=subprocess.check_output(['git','ls-files'],text=True).splitlines()
files=[f for f in files if (f.startswith(prefixes) and (f.endswith('.rs') or Path(f).name in ['Cargo.toml','Cargo.lock'])) or f in ['Cargo.toml','Cargo.lock']]
files+=['crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/RealR1_client_tests.rs']
files=sorted(set(files))
pins={f:hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}
W='/home/dombarker/project-offloads/codex-cx-real-r1-20261023/client'
script='''
import hashlib,json,subprocess
from pathlib import Path
W=Path(WORKSPACE);files=FILES
pins={f:hashlib.sha256((W/'src'/f).read_bytes()).hexdigest() for f in files}
artifacts=[]
expected={'default':'40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0','devnet':'12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
for mode in expected:
    name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'
    actual=W/'artifacts'/mode/name
    reference=Path('/home/dombarker/project-offloads/codex-cx-ct-kernels-v2-20261022/artifacts')/('v2final-'+mode)/name
    sha=hashlib.sha256(actual.read_bytes()).hexdigest()
    row=dict(mode=mode,sha256=sha,bytes=actual.stat().st_size,expected_sha256=expected[mode],match=sha==expected[mode])
    if reference.exists():
        row.update(reference=str(reference),cmp_exit_status=subprocess.run(['cmp','-s',str(actual),str(reference)]).returncode)
    artifacts.append(row)
print(json.dumps(dict(pins=pins,artifacts=artifacts,rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True),source_workspace=str(W/'src'))))
'''.replace('WORKSPACE',repr(W)).replace('FILES',repr(files))
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
assert pins==remote['pins']
assert all(a['match'] and a.get('cmp_exit_status',0)==0 for a in remote['artifacts'])
remote.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_count=len(files),
              status='ALL SOURCE HASHES MATCH; FULL ELF HASHES MATCH',working_tree_additions_included=True)
(R/'client/source-pins.json').write_text(json.dumps(remote,indent=2)+'\n')
print(json.dumps(dict(source_count=len(files),artifacts=remote['artifacts'])))
