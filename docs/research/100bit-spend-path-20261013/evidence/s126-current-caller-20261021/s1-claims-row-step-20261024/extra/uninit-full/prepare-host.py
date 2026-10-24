#!/usr/bin/env python3
"""Isolate a proof-only copy; retained native bodies are never edited in place."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');W=H/'s1-claims-row-step-v1-20261024';assert W.exists()
base=H/'s1-claim-word-partition-v1-20261024'
for name in ['frozen-probe','frozen-source']:
 shutil.copytree(base/name,W/name,ignore=shutil.ignore_patterns('target','.git'))
shutil.copyfile(base/'Cargo.lock',W/'Cargo.lock')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['r1_semantic.rs','r1_wire.rs']:
 shutil.copyfile(W/'payload'/name,W/'frozen-probe/src'/name)
sem=W/'frozen-probe/src/r1_semantic.rs';sem.write_text(sem.read_text()+'\n#[cfg(kani)]\n#[path="claims_write_proofs.rs"]\nmod claims_write_proofs;\n')
wire=W/'frozen-probe/src/r1_wire.rs';wire.write_text(wire.read_text()+'''\n#[cfg(kani)]
pub(crate) fn s1_claims_probe_record(row:u8,framed:&[u8])->ValidatedRecord<'_>{
 ValidatedRecord{row,framed}
}
''')
shutil.copyfile(W/'proofs.rs',W/'frozen-probe/src/claims_write_proofs.rs')
(W/'Cargo.toml').write_text('[workspace]\nmembers=["frozen-probe"]\nexclude=["frozen-source/crates/aspis-statement"]\nresolver="2"\n[profile.release]\nopt-level=3\noverflow-checks=true\n')
meta=json.loads((W/'payload/source-pins.json').read_text())
for name,row in meta['frozen_files'].items():assert sha(W/'payload'/name)==row['sha256']
# Verify the exact shipped pointer-write expression, with the decoder callee
# still present. No replacement of its record/token or input offset.
fragment='''out.as_mut_ptr()
                .cast::<[QM31; 29]>()
                .add(p)
                .write(record.decode_k::<29>(p * 29)?);'''
normalize=lambda s:''.join(s.split())
assert normalize(fragment) in normalize((W/'payload/r1_semantic.rs').read_text())
assert normalize(fragment) in normalize((W/'proofs.rs').read_text())
meta.update(fragment=fragment,proof_sha256=sha(W/'proofs.rs'),base=str(base),qualification='One initialized-prefix native loop step at a verified decoder normal-return cut; not claims allocation/cleanup, whole claims, arbitrary SDK/SBF or whole soundness closure.')
(W/'source-binding.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(prepared=str(W))))
