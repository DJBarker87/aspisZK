#!/usr/bin/env python3
"""Full native gamma/ordinary values vs exact already-extracted owned reference functions."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1]);F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
original=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R,text=True)
refpath=R/'docs/research/100bit-spend-path-20261013/lean-candidates/post25-indexed-addsmall-source-model-20261020/extraction/candidate-input/lib.rs';reference=refpath.read_text()
markers=['fn qm31_div_pass(','fn low_base_p_digits(','fn decode8(','fn add_small_base_p(','pub fn ordinary_sample(','pub fn gamma_sample(']
ref='use aspis_core::field::{WideExact, CM31, M31, P, QM31};\n'+'\n'.join(item(reference,k)for k in markers)+'\n'
# Native core types/constructors replace NO fields: both sides use actual frozen core.
(O/'min/src/equality_actual.rs').write_text(original);(O/'min/src/equality_reference.rs').write_text(ref)
root='#![no_std]\nextern crate alloc;\n#[path="equality_actual.rs"]pub mod actual;\n#[path="equality_reference.rs"]pub mod reference;\n'
root+='#[cfg(kani)] mod value_proofs {\nfn same(a:aspis_core::field::WideExact,b:aspis_core::field::WideExact){let a=a.to_limbs();let b=b.to_limbs();let mut j=0;while j<8{assert!(a[j]==b[j]);j+=1;}}\n#[kani::proof] #[kani::unwind(10)] fn ordinary_value_equal(){let block=kani::any::<[u8;32]>();same(crate::actual::ordinary_sample(&block),crate::reference::ordinary_sample(&block));kani::cover!(true,"both ordinary samplers return");}\n#[kani::proof] #[kani::unwind(10)] fn gamma_value_equal(){let block=kani::any::<[u8;32]>();same(crate::actual::gamma_sample(&block),crate::reference::gamma_sample(&block));kani::cover!(true,"both gamma samplers return");}\n}\n'
(O/'min/src/probe_public.rs').write_text(root)
p=O/'min/Cargo.toml';p.write_text(p.read_text().replace('src/probe_prepared_claim.rs','src/probe_public.rs'))
(T/'reference.rs').write_text(ref);(T/'proofs.rs').write_text(root)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'public-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze=F,reference_source=str(refpath.relative_to(R)),reference_sha256=hashlib.sha256(refpath.read_bytes()).hexdigest(),selected_functions=markers,domain='Every typed32-byte block, all8 actual native resultwords, no callee stubs. Reference selected complete function bodies; actual core types/constructors on both sides, no simplified replacement carriers.',remaining='Kani pending; existing Lean reference-to-rank proofs still need exact caller/source composition, SDK/oracle/runtime/release remain open.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),native_stubs=0)))
