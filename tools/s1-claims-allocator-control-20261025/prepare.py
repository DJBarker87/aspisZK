#!/usr/bin/env python3
"""Reconstruct a fresh source-only paired probe. Does not run any compiler."""
from pathlib import Path
import argparse,hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
a=argparse.ArgumentParser();a.add_argument('--out',required=True);args=a.parse_args()
O=Path(args.out);O.mkdir(mode=0o700,exist_ok=False)
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
candidate=subprocess.check_output(['git','rev-parse','891a213f79'],cwd=R,text=True).strip()
get=lambda revision,path:subprocess.check_output(['git','show',revision+':'+path],cwd=R)
sha=lambda b:hashlib.sha256(b).hexdigest();files={}
def put(path,data):
 p=O/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);files[path]=sha(data)
base=json.loads((E/'s1-init-local-20261025/source-binding.json').read_text())
for row in base['native_source_files']:
 if row['path'].startswith('core-workspace/'):
  data=get(freeze,row['source']);assert sha(data)==row['sha256'];put(row['path'],data)
put('core-workspace/Cargo.toml',(E/'s1-claims-allocator-control-v4/source/core-workspace/Cargo.toml').read_bytes())
for rel in ['Cargo.toml','Cargo.lock']:
 put('min/'+rel,(E/'s1-claims-allocator-control-v4/source/min'/rel).read_bytes())
put('min/src/sampler.rs',get(freeze,'crates/aspis-r1-cost-probe/src/sampler.rs'))
wire=get(freeze,'crates/aspis-r1-cost-probe/src/r1_wire.rs')+b'''
#[cfg(kani)]
pub(crate) fn s1_claims_probe_record(row:u8,framed:&[u8])->ValidatedRecord<'_>{
 ValidatedRecord{row,framed}
}

#[cfg(kani)]
pub(crate) fn s1_claims_probe_prefix<'a>(root:&'a[u8;32],frame:&'a[u8])->Prefix<'a>{Prefix{c1_root:root,records:[frame;27]}}
'''
put('min/src/allocator_wire.rs',wire)
original=get(freeze,'crates/aspis-r1-cost-probe/src/r1_semantic.rs').decode()
x=original.index('#[inline(never)]\nfn claims(');y=original.index('\n#[inline(never)]',x+1);body=original[x:y]
header='use crate::r1_wire::{self as wire,Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'
candidate_path='docs/research/100bit-spend-path-20261013/rust-candidates/s1-claims-safe-storage-20261025/claims.rs'
cb=get(candidate,candidate_path).decode();assert cb==(B/'rust-candidates/s1-claims-safe-storage-20261025/claims.rs').read_text()
put('min/src/allocator_claims.rs',(header+cb+'\n#[cfg(kani)]\n#[path="allocator_claims_proofs.rs"]\nmod proofs;\n').encode())
put('min/src/allocator_original.rs',(header+body+'''
#[cfg(kani)]
pub(crate) fn run(prefix:&Prefix<'_>)->Result<Box<[[QM31;29];3]>,Error>{claims(prefix)}
''').encode())
put('min/src/allocator_claims_proofs.rs',(T/'proofs.rs').read_bytes())
put('min/src/probe_claims_allocator.rs',(T/'probe.rs').read_bytes())
(O/'binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=freeze,
 candidate_revision=candidate,candidate_source=candidate_path,candidate_sha256=sha(cb.encode()),
 frozen_whole_source_sha256=sha(original.encode()),frozen_claims_sha256=sha(body.encode()),
 frozen_claims_span=dict(offset=x,length=y-x),files=files,
 status='SOURCE_ONLY',compiler_launched=False,solver_launched=False,host_SSH_operations=0,
 qualification='Complete function bodies in factored modules, two wire test constructors and one original private-function forwarding wrapper. Not whole-crate/ABI/context/release identity or candidate adoption.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),path=str(O))))
