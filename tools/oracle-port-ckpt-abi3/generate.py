#!/usr/bin/env python3
"""Exact private reader excerpts; never mutate the shipped crate.
The generated Rust is an excerpt proof boundary, not linked resume adoption.
"""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2]
p=R/'crates/aspis-r1-cost-probe/src/verifier.rs';s=p.read_text()
start=s.index("struct Reader<'a>");end=s.index('#[inline(never)]\npub fn resume',start)
text=s[start:end]
out=R/'tools/oracle-port-ckpt-abi3/src/reader-source.rs'
record={'source':str(p.relative_to(R)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'byte_start':len(s[:start].encode()),'byte_end':len(s[:end].encode()),'excerpt_sha256':hashlib.sha256(text.encode()).hexdigest(),'normalization':'none; byte-exact contiguous excerpt','scope':'Reader raw/e/k, query validator, semantic-alpha and weights helpers; not the resume caller'}
manifest=out.parent.parent/'reader-source.json'
if '--check' in sys.argv:
 assert out.read_text()==text
 assert json.loads(manifest.read_text())==record
else:
 out.write_text(text);manifest.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))

# Byte-exact authentication prefix, before the first field-section read.
a=s.index('    if bytes.len()!=checkpoint_size(v)',s.index('pub fn resume'))
b=s.index('    let mut r=Reader{bytes,at:80}',a)
prefix=s[a:b]
wrapper='use aspis_r1_cost_probe::verifier::checkpoint_size;\nfn authenticate<H:Digest32>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,hash:H)->Result<usize,Error> {\n'+prefix+'    Ok(end)\n}\n'
w=out.parent/'authentication-source.rs'
m=out.parent.parent/'authentication-source.json'
meta=dict(source=record['source'],source_sha256=record['source_sha256'],byte_start=len(s[:a].encode()),byte_end=len(s[:b].encode()),excerpt_sha256=hashlib.sha256(prefix.encode()).hexdigest(),normalization='none in body; return Ok(end) replaces remaining reader suffix',scope='exact resume guards and ordered digest checks only')
if '--check' in sys.argv:
 assert w.read_text()==wrapper
 assert json.loads(m.read_text())==meta
else:
 w.write_text(wrapper);m.write_text(json.dumps(meta,indent=2)+'\n')
