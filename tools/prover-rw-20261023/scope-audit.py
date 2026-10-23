#!/usr/bin/env python3
"""Pin changed native files and assess verifier rebuild trigger; no ELF claim."""
from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parents[2]
base='084f714ccd'
paths=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],cwd=r,text=True).splitlines()
allowed={'crates/aspis-r1-cost-probe/Cargo.toml','crates/aspis-r1-cost-probe/src/prover.rs'}
assert set(paths)<=allowed,paths
example='crates/aspis-r1-cost-probe/examples/prover_rw_gate.rs'
paths=sorted(set(paths+[example]))
record=dict(base=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),
    files={p:dict(sha256=hashlib.sha256((r/p).read_bytes()).hexdigest(),bytes=(r/p).stat().st_size) for p in paths},
    scope='One feature-gated host module plus a host-only example declaration. No verifier source changed.',
    module_gate='lib.rs: #[cfg(feature = "prover")] pub mod prover; program-build never enables prover',
    elf_rebuild_run=False,elf_identity_claim=False,
    expected_elf_sha256={'default':'d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0','devnet':'2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},
    pin_source='evidence/s2x-20261023/boundary-inventory.json; inherited pins, not rebuilt here',
    print_axioms='N/A: source scope audit')
print(json.dumps(record,indent=2))
