#!/usr/bin/env python3
"""Actual optimized wide helper vs already-extracted owned indexed helper; same full32-byte/8-word carriers."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1]);F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
original=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R,text=True)
reference=(R/'docs/research/100bit-spend-path-20261013/lean-candidates/post25-indexed-sampler-candidate-20261019/sources/sampler.rs').read_text()
body=item(reference,'fn low_base_p_digits(')
# The source reference uses the same indexed pass already proved in Lean.
assert item(reference,'fn qm31_div_pass(')==item(original,'fn qm31_div_pass(')
code=original+'\n#[cfg(kani)] mod value_proofs {use super::*;\n'+body.replace('fn low_base_p_digits(','fn owned_low_base_p_digits(')+"\n#[kani::proof] #[kani::unwind(10)] fn low_base_value_equal(){let block=kani::any::<[u8;32]>();let(a,q)=low_base_p_digits(&block);let(b,r)=owned_low_base_p_digits(&block);let mut i=0;while i<8{assert!(a[i]==b[i]);i+=1;}assert!(q==r);kani::cover!(true,\"actual andowned helper return\");}\n}\n"
(O/'min/src/value_sampler.rs').write_text(code)
(O/'min/src/probe_value.rs').write_text('#![no_std]\nextern crate alloc;\n#[path="value_sampler.rs"] pub mod sampler;\n')
p=O/'min/Cargo.toml';s=p.read_text().replace('src/probe_prepared_claim.rs','src/probe_value.rs');p.write_text(s)
(T/'value_sampler.rs').write_text(code)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'value-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze=F,original_sampler_sha256=hashlib.sha256(original.encode()).hexdigest(),reference_body=body,domain='Every typed32-byte block; complete8 u32 outputdigits andu32 quotient, no callee stubs/assumed arithmetic. Source-only test append; no protocol adoption.',remaining='Kani required; equality is helper boundary only, not SDK/oracle/release or wholeS1S6.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',source_files=len(files),stubs=0)))
