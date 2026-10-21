#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
out=Path(sys.argv[1]);(out/'src').mkdir(parents=True,exist_ok=True)
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
p='crates/aspis-r1-cost-probe/src/r1_wire.rs';s=(R/p).read_text();assert subprocess.check_output(['git','show','b2727acd3:'+p])==(R/p).read_bytes()
markers=['pub const fn row_shape(','pub struct Prefix<','pub(crate) struct ValidatedRecord<',"fn parse_record_at<'a>",'pub fn parse(bytes:','pub fn record(&self,','pub fn payload(&self,','pub(crate) fn validated_record(&self,']
items={m:item(s,m) for m in markers}
code='''#![allow(dead_code,private_interfaces)]
const CLAIMS:usize=87;const LANES:usize=29;
#[derive(Debug,Clone,Copy,PartialEq,Eq)] enum Error {Length{row:u8},InvalidRow,TrailingBytes,Rejected{row:u8}}
static mut FAIL_ROW:u8=255;
fn parse_record(row:u8,_record:&[u8])->Result<(),Error>{if row==unsafe{FAIL_ROW}{Err(Error::Rejected{row})}else{Ok(())}}
'''+items[markers[0]]+'\n'+items[markers[1]]+'\n'+items[markers[2]]+'\n'+items[markers[3]]+"\nimpl<'a> Prefix<'a> {\n"+'\n'.join(items[m] for m in markers[4:])+'\n}\n'+(R/'tools/s2-kani-20261021/parser-harness.rs').read_text()
(out/'src/lib.rs').write_text(code);(out/'Cargo.toml').write_text('[package]\nname="aspis-s2-parser-kani"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
manifest=dict(schema='s2-parser-source-cut-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources={p:hashlib.sha256((R/p).read_bytes()).hexdigest()},exact_bodies=items,code_sha256=hashlib.sha256(code.encode()).hexdigest(),qualification='Exact parser caller, helper and token accessors. Child parse_record abstracted by arbitrary first failing row; no canonicality proof claimed. All wrapper observations are addresses/lengths; no backing bytes read by these exact bodies except root reference conversion. Zero buffer does not establish content validity.')
(out/'source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n');(E/'parser-source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n')
# The owned range reference is also extracted independently.
ref=out.parent/'reference-parser';(ref/'src').mkdir(parents=True,exist_ok=True)
reference=(R/'tools/s2-kani-20261021/parser-harness.rs').read_text().split('#[cfg(kani)]')[0]
(ref/'src/lib.rs').write_text('const CLAIMS:usize=87;const LANES:usize=29;\n'+items[markers[0]]+'\npub '+reference)
(ref/'Cargo.toml').write_text('[package]\nname="aspis-s2-parser-reference"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
