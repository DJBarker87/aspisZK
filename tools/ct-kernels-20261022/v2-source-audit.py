#!/usr/bin/env python3
"""Read-only scope/provenance checks for the v2 candidate."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];BASE='c6be35873e';STAGE2='cad5e1876d'
def original(rev,path):return subprocess.check_output(['git','show',rev+':'+path],cwd=R)
def changed(*paths):return subprocess.check_output(['git','diff','--name-only',BASE,'--',*paths],cwd=R).decode().splitlines()
allowed={
 'crates/aspis-core/Cargo.toml','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-core/src/field/wide_exact.rs',
 'crates/aspis-prover/Cargo.toml','crates/aspis-r1-cost-probe/Cargo.toml','crates/aspis-r1-cost-probe/examples/ct_fixture_gate.rs',
 'crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/trace.rs',
 'crates/aspis-r1-cost-probe/src/host_semantic.rs','crates/aspis-r1-cost-probe/src/ct_pole.rs'}
assert set(changed('crates','programs'))==allowed
inherited=[]
for p in sorted(allowed-{'crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/host_semantic.rs','crates/aspis-r1-cost-probe/src/ct_pole.rs'}):
 assert (R/p).read_bytes()==original(STAGE2,p),p
 inherited.append(dict(path=p,sha256=hashlib.sha256((R/p).read_bytes()).hexdigest(),unchanged_from_stage2=True))
# These are the deliberately excluded stage-3 production files.
excluded=['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-core/src/r0_transcript.rs','crates/aspis-statement/src/constraints_v4.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/multiproof.rs']
for p in excluded:
 ref=STAGE2 if p.endswith('/prover.rs') else BASE
 assert (R/p).read_bytes()==original(ref,p),p
for commit in ['93e85cd4f3','7eed88696f','def2508a2d','44bfbb3313','edff2eb4ad','47397e5e16']:
 assert subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=R).returncode==1
assert not changed('programs','crates/aspis-statement','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3')
provenance=json.loads(subprocess.check_output(['python3',str(R/'tools/ct-kernels-20261022/pole-instrument.py')],cwd=R))
# Verify generated instrumentation is tracked and current.
for p in ['pole-instrumented.rs','pole-compression.rs','pole-compression-reference.rs','pole-compression-instrumented.rs']:
 assert (R/'tools/ct-kernels-20261022'/p).read_bytes()==original('HEAD','tools/ct-kernels-20261022/'+p),p
print(json.dumps(dict(research_base=BASE,revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip(),production_allowlist=sorted(allowed),stage2_inherited_sources=inherited,stage3_commits_absent=True,stage3_sources_absent=True,statement_program_checker_sources_unchanged=True,pole_source_check=provenance,classification='source-scope/provenance audit; not compiler/hardware constant-time proof'),indent=2))
