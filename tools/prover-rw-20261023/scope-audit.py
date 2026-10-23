#!/usr/bin/env python3
"""Pin changed native files and assess verifier rebuild trigger; no ELF claim."""
from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parents[2]
base='084f714ccd'
paths=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],cwd=r,text=True).splitlines()
allowed={'crates/aspis-r1-cost-probe/'+p for p in [
 'Cargo.toml','examples/prover_rw_gate.rs','examples/prover_rw_differential.rs',
 'src/lib.rs','src/prover.rs','src/host_commitment.rs','src/host_semantic.rs',
 'src/host_sumcheck.rs','src/host_tree.rs','src/host_transcript.rs','src/host_wire.rs','src/host_compact.rs']}
allowed.update({'crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-prover/src/state_only_hiding.rs','crates/aspis-prover/src/state_only_entropy_prover_rw_kani.rs'})
paths+=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','crates','programs'],cwd=r,text=True).splitlines()
assert set(paths)<=allowed,paths
assert '#[cfg(kani)]\n#[path="state_only_entropy_prover_rw_kani.rs"]\nmod prover_rw_kani;' in (r/'crates/aspis-prover/src/state_only_entropy.rs').read_text()
example='crates/aspis-r1-cost-probe/examples/prover_rw_gate.rs'
paths=sorted(set(paths+[example]))
record=dict(base=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()+('+working-tree' if subprocess.run(['git','diff','--quiet','HEAD','--','crates','programs'],cwd=r).returncode else ''),
    files={p:dict(sha256=hashlib.sha256((r/p).read_bytes()).hexdigest(),bytes=(r/p).stat().st_size) for p in paths},
    scope='Selected host-only prover modules and optional aspis-prover dependency; shared verifier sources and core field/hash kernels unchanged.',
    module_gate='All changed host_* and prover modules require prover; aspis-prover is optional and prover-gated. Program manifests enable program-build, not prover/ct-host-prover.',
    elf_rebuild_run=True,elf_identity_claim='See continuation/elf-byte-comparison-proverw002.json for literal full-file comparison; later host-only source edits require closure assessment, not an unchanged SBF replay',
    expected_elf_sha256={'default':'d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0','devnet':'2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},
    pin_source='continuation/elf-identities.json and elf-byte-comparison-proverw002.json; actual capped proverw002 rebuilds and retained S2E artifacts',
    print_axioms='N/A: source scope audit')
print(json.dumps(record,indent=2))
