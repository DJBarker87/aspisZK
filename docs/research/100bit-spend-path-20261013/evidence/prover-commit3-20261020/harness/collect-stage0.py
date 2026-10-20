#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit3-20261020')
F=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
expected={'default':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','devnet':'fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
r={'source_revision':'6593c0c21','stage':0,'source_changes_for_gate':False,'programs':{},'dependency_inventory':json.loads((H/'dependency-inventory.json').read_text()),'inventory_scope':'All resolved normal and build dependencies for each frozen SBF feature set (including proc macros/build-only dependencies); cargo tree with pinned platform-tools rustc. Does not assert every dependency contributes retained machine instructions.','reservation_before_build':{'observed_other_populated_scopes':3,'sum_other_memory_max_bytes':3*8*2**30,'this_job_memory_max_bytes':8*2**30,'total_gib':32,'safe_limit_gib':55},'print_axioms':'N/A: SBF rebuild and dependency inventory; no new Lean declaration','gate_reruns':'No runtime source change and all ELFs identical: conditional requirement to move refactors and rerun fixed-seed/library/D78/P_R1 gates is not triggered.'}
for mode,want in expected.items():
    name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'
    p=H/'artifacts'/mode/name; data=p.read_bytes(); got=hashlib.sha256(data).hexdigest()
    cmp=subprocess.run(['cmp','--silent',str(p),str(F/'artifacts'/mode/name)]).returncode
    receipt=json.loads((H/'receipts'/('build-'+mode)/'receipt.json').read_text())
    assert got==want and cmp==0 and receipt['exit_status']==0
    assert r['dependency_inventory'][mode]['exit']==0
    r['programs'][mode]={'sha256':got,'expected_sha256':want,'size_bytes':len(data),'cmp_exit':cmp,'byte_identical':True,'receipt':receipt}
files=['Cargo.toml','Cargo.lock','programs/r1-cost-probe/Cargo.toml','programs/aspis-pool/Cargo.toml']
for d in ['crates/aspis-core','crates/aspis-statement','crates/aspis-r1-cost-probe','crates/aspis-prover','programs/r1-cost-probe','programs/aspis-pool']:
    files += [str(p.relative_to(H/'src')) for p in (H/'src'/d).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']]
r['source_pins']={f:hashlib.sha256((H/'src'/f).read_bytes()).hexdigest() for f in sorted(set(files))}
r['prover_cfg']={'lib_rs':'crates/aspis-r1-cost-probe/src/lib.rs:20-21','guard':'#[cfg(feature = "prover")] pub mod prover;','enabled_for_either_program':False,'aspis_prover_in_program_dependency_closure':False}
for v in r['dependency_inventory'].values():
    assert not any(c.startswith('aspis-prover ') for c in v['crates'])
(H/'frozen-source-check.json').write_text(json.dumps(r,indent=2)+'\n')
print('All three SHA256 and byte comparisons pass')
