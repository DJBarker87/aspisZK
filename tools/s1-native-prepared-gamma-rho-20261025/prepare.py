#!/usr/bin/env python3
"""Next small binding: one actual wide gamma sampler, retaining checked native rho."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-rho-20261025/prepare.py'),str(O)],check=True)
p=O/'min/src/prepared_claim_native/proofs.rs';s=p.read_text()
a='STAGE=2;SCALARS[0]';b='let actual=crate::sampler_native::gamma_sample(block);SCALARS[0]=actual;canonical_e(actual);assert!(actual.to_limbs().iter().any(|&x|x!=0));STAGE=2;actual';assert s.count(a)==1;s=s.replace(a,b)
a='same_e(out.gamma,scalars[0])';assert s.count(a)==1;s=s.replace(a,'same_e(out.gamma,unsafe{SCALARS[0]})')
s+='\nfn canonical_e(x:E){let limbs=x.to_limbs();let mut j=0;while j<8{assert!(limbs[j]<aspis_core::field::P);j+=1;}}\n'
p.write_text(s);(T/'proofs.rs').write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'gamma-rho-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',normal_primitive_cuts=6,domain='Same canonical928-byte payload/native semantic carriers andarbitrary33 reply blocks. Gamma andrho are actual native sampler outputs logged at reached calls; all8/4 coordinates, nonzero gamma andsubsequent uses/returned Prepared checked.',remaining='Verification pending; ordinary/query-pair/mul/add/dotpush/finish cuts plus scripted digest; SDK/runtime/init/extraction/oracle/release remain open.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),normal_primitive_cuts=6)))
