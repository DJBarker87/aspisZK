#!/usr/bin/env python3
"""Actual frozen native samplers in the complete current-source constructor/claim gate."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
p=O/'min/src/probe_prepared_claim.rs';s=p.read_text();s+='\n#[path="sampler.rs"] pub mod sampler_native;\n';p.write_text(s)
p=O/'min/src/prepared_claim_native/proofs.rs';s=p.read_text()
changes=[
('STAGE=2;SCALARS[0]','let actual=crate::sampler_native::gamma_sample(block);SCALARS[0]=actual;canonical_e(actual);assert!(actual.to_limbs().iter().any(|&x|x!=0));STAGE=2;actual'),
('same_bytes(block,&HASHES[3*n-1]);STAGE=n+1;SCALARS[n-1]','same_bytes(block,&HASHES[3*n-1]);let actual=crate::sampler_native::ordinary_sample(block);SCALARS[n-1]=actual;canonical_e(actual);STAGE=n+1;actual'),
('STAGE=7;RHO','let actual=crate::sampler_native::qm31_sample(block);RHO=actual;canonical_q(actual);STAGE=7;actual'),
('let scalars=any_es::<4>();','let scalars=[E::ZERO;4];'),
('let rho=any_q();','let rho=QM31::ZERO;'),
('let hashes=kani::any::<[[u8;32];33]>();','let hashes=kani::any::<[[u8;32];33]>();')]
for a,b in changes:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
s+='\nfn canonical_e(x:E){let limbs=x.to_limbs();let mut j=0;while j<8{assert!(limbs[j]<aspis_core::field::P);j+=1;}}\nfn canonical_q(x:QM31){assert!(x.c0.a.0<aspis_core::field::P);assert!(x.c0.b.0<aspis_core::field::P);assert!(x.c1.a.0<aspis_core::field::P);assert!(x.c1.b.0<aspis_core::field::P);}\n'
assert s.count('same_q(out.rho,rho)')==1;s=s.replace('same_q(out.rho,rho)','same_q(out.rho,unsafe{RHO})')
for i in range(4):
 a='scalars['+str(i)+']';b='unsafe{SCALARS['+str(i)+']}'
 # Only final returned-field comparisons read the old local placeholders.
 needle0=['same_e(out.gamma,','same_e(out.kappa,','same_e(out.alpha[0],','same_e(out.alpha[1],'][i]+a+')'
 assert s.count(needle0)==1;s=s.replace(needle0,needle0.replace(a,b))
p.write_text(s);(T/'proofs.rs').write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'samplers-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',changes=changes,normal_primitive_cuts=5,sampler_binding='Two module paths compile exactly the same frozen sampler.rs against the same native core types. The observational hooks call the un-stubbed path and return its actual native value, checking all native coordinates/canonicality and nonzero gamma. No sampler reply is arbitrary.',domain='Canonical928-byte y1 and native semantic carriers; arbitrary33 digest reply blocks. SCALARS/RHO are zero-initialized ghost output logs, populated by each actual sampler return inside the constructor. No extra sampler executions or independently arbitrary sampled values. Full returned Prepared fields and all later uses are compared to those same logged native values. Scripted digest and actual query-pair/mul/add/dot result cuts remain.',remaining='Kani required; concrete SDK/stage1/stdlib/runtime/allocator/extraction, mathematical sampling-law/source-event transport, coherent source joins and release artifacts remain open.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),normal_primitive_cuts=5)))
