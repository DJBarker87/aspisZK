#!/usr/bin/env python3
"""Cut exact frozen header body and an owned, translatable header reference."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
out=Path(sys.argv[1]); (out/'src').mkdir(parents=True,exist_ok=True)
def item(s,marker):
 a=s.index(marker); b=s.index('{',a); d=1;e=b+1
 while d:
  d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
paths=['crates/aspis-r1-cost-probe/src/'+n for n in ['candidate.rs','compact.rs','transport.rs']]
texts={p:(R/p).read_text() for p in paths}
for p in paths:
 frozen=subprocess.check_output(['git','show','b2727acd3:'+p])
 assert frozen==(R/p).read_bytes(),p
body=item(texts[paths[0]],'pub fn parse_shape(')
assert 'Self::S2 => 2' in texts[paths[2]] or 'Self::S2=>2' in texts[paths[2]]
reference='''pub fn header_reference(length:usize, magic:bool, tag:u8, tail:bool)->bool {
    length==57607 && magic && tag==2 && tail
}
'''
code='''#![allow(dead_code)]
#[derive(Debug,Clone,Copy,PartialEq,Eq)] enum Variant {S2}
impl Variant {fn tag(self)->u8 {2}}
#[derive(Debug,Clone,Copy,PartialEq,Eq)] enum Error {Parse}
mod compact {pub const PROOF_BYTES:usize=57607;pub const MAGIC:&[u8;8]=b"R1P3CB18";}
'''+body+'\n'+reference+(R/'tools/s2-kani-20261021/header-harness.rs').read_text()
(out/'src/lib.rs').write_text(code)
(out/'Cargo.toml').write_text('[package]\nname="aspis-s2-header-kani"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
manifest=dict(schema='s2-header-source-cut-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),freeze='b2727acd3',sources={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths},exact_body=body,reference=reference,code_sha256=hashlib.sha256(code.encode()).hexdigest(),boundary='Exact parse_shape body. Variant::S2.tag and constants supplied from frozen definitions. Only header reads; suffix supplied as zero in Kani, independence checked by body census.')
(out/'source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n')
(E/'header-source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n')
ref=out.parent/'reference';(ref/'src').mkdir(parents=True,exist_ok=True)
(ref/'src/lib.rs').write_text(reference)
(ref/'Cargo.toml').write_text('[package]\nname="aspis-s2-header-reference"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
