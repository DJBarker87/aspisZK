#!/usr/bin/env python3
"""One sampler binding at a time: native rho inside the complete current constructor/claim."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
p=O/'min/src/probe_prepared_claim.rs';p.write_text(p.read_text()+'\n#[path="sampler.rs"] pub mod sampler_native;\n')
p=O/'min/src/prepared_claim_native/proofs.rs';s=p.read_text();a='STAGE=7;RHO';b='let actual=crate::sampler_native::qm31_sample(block);RHO=actual;canonical_q(actual);STAGE=7;actual';assert s.count(a)==1;s=s.replace(a,b)
s=s.replace('let rho=any_q();','let rho=QM31::ZERO;')
s+='\nfn canonical_q(x:QM31){assert!(x.c0.a.0<aspis_core::field::P);assert!(x.c0.b.0<aspis_core::field::P);assert!(x.c1.a.0<aspis_core::field::P);assert!(x.c1.b.0<aspis_core::field::P); }\n'
assert s.count('same_q(out.rho,rho)')==1;s=s.replace('same_q(out.rho,rho)','same_q(out.rho,unsafe{RHO})')
p.write_text(s);(T/'proofs.rs').write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'rho-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',normal_primitive_cuts=7,domain='Canonical928-byte y1, native semantic carriers andarbitrary33 digest reply blocks. RHO isactual native qm31_sample result logged during the source scalar_k call, no independently arbitrary rho reply. All4 returned coordinates and all subsequent Prepared fields remain checked.',remaining='Native verification required; gamma/ordinary/query-pair/mul/add/dotpush/finish cuts and scripted digest remain. No SDK/runtime/extraction/oracle/release closure.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),normal_primitive_cuts=7)))
