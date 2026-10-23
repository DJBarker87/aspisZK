#!/usr/bin/env python3
"""Exact original outer-loop body versus reference helper, on full actual types.
Only leaf calls are paired; source scalar checks, dot push, range and parts
updates remain actual Rust. No shipped source is edited.
"""
from pathlib import Path
import subprocess,sys,json,hashlib,importlib.util
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
spec=importlib.util.spec_from_file_location('base',R/'tools/s1-claim-source-steps-20261023/prepare.py');base=importlib.util.module_from_spec(spec)
# The base generator obtains the complete adopted source dependency snapshot.
subprocess.run(['python3',str(spec.origin),str(O)],check=True)
B=json.loads((O/'source-binding.json').read_text());original=B['original_claim']
a=original.index('for point in 0..6 {')+len('for point in 0..6 {');end=a;depth=1
while depth:depth+=(original[end]=='{')-(original[end]=='}');end+=1
body=original[a:end-1]
args='''<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,parts:&mut[E;7])->Result<(),Error>'''
old='fn original_point_step'+args+' {\n'+body+'\n Ok(())\n}\n'
new='fn reference_point_step'+args+' {\n parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;\n Ok(())\n}\n'
p=O/'src/lib.rs';p.write_text(p.read_text()+old+new)
# A proof-only public alias permits naming the existing private raw leaf in
# a Kani attribute. No constructor, type field or executable body is changed.
alias='\n#[cfg(kani)] pub use canonical::Q as ProofQ;\n';p=O/'src/fast_pairing.rs';pairing=p.read_text();assert pairing.count('        fn raw(')==1
pairing=pairing.replace('        fn raw(','        pub fn raw(',1);p.write_text(pairing+alias)
(O/'src/proofs.rs').write_bytes((Path(__file__).parent/'proofs.rs').read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'point-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=B['revision'],original_claim_sha256=hashlib.sha256(original.encode()).hexdigest(),original_outer_body=body,old_step=old,reference_step=new,proof_only_alias=alias,proof_only_visibility="Q.raw private to public; executable body unchanged",qualification=__doc__,source_sha256=sha(O/'src/lib.rs'),pairing_source_sha256=sha(O/'src/fast_pairing.rs'),proof_sha256=sha(O/'src/proofs.rs'),remaining='Source/callee interpretation and whole original caller join are not assumed discharged by this paired-leaf certificate.'),indent=2)+'\n')
