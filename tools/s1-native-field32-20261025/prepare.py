#!/usr/bin/env python3
"""Materialize one focused field32 source target; never executes tools."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
W=Path('/private/tmp/s126-kani-local-diagnostic-20261025-v1');C=W/'field32';C.mkdir(exist_ok=False);(C/'src').mkdir()
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
s=subprocess.check_output(['git','show',freeze+':crates/aspis-r1-cost-probe/src/weights.rs'],cwd=R).decode();a=s.index('pub fn field(');z=s.index('\n',a);body=s[a:z]
(C/'src/weights.rs').write_text('use aspis_core::{field::WideExact as E,r0::CodeField};\n'+body+'\n')
(C/'src/lib.rs').write_text('#![no_std]\npub mod weights;\n#[cfg(kani)] mod proofs;\n')
(C/'src/proofs.rs').write_bytes((T/'proofs.rs').read_bytes())
manifest=(W/'min/Cargo.toml').read_text();manifest=manifest[:manifest.index('[lib]')]+'[lib]\npath="src/lib.rs"\n';(C/'Cargo.toml').write_text(manifest);(C/'Cargo.lock').write_bytes((W/'min/Cargo.lock').read_bytes())
(T/'source-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=freeze,whole_weights_sha256=hashlib.sha256(s.encode()).hexdigest(),selected_field=body,field_sha256=hashlib.sha256(body.encode()).hexdigest(),scope='All928-byte inputs whose symbolically selected32-byte record is canonical; other896 bytes arbitrary. Exact eight returned native E words and native c0 coordinates; no stub, no decoder substitute. Not total on noncanonical selected records.',compiler_launched=False,solver_launched=False),indent=2)+'\n')
print(json.dumps(dict(source_only=True,crate=str(C))))
