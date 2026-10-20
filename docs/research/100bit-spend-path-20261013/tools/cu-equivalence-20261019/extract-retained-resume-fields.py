#!/usr/bin/env python3
"""Exact resume decoder fragments, with mutable Reader handbacks exposed."""
from pathlib import Path
import argparse,subprocess,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'retained-resume-fields-input';sha=lambda b:hashlib.sha256(b).hexdigest()
base=tool/'rho-resume-caller-input';old=(base/'fragments/original-resume.rs').read_bytes()
for rev in ['f458169f705f25b04e1e29546c621e4665e0f64c','39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 src=subprocess.check_output(['git','-C',str(repo),'show',rev+':crates/aspis-r1-cost-probe/src/verifier.rs'])
 assert old in src,rev
begin=b'let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];'
semantic=b'let mut semantic_alpha=[K::ZERO;10];for x in &mut semantic_alpha {*x=r.k()?;}'
assert old.count(begin)==1 and old.count(semantic)==1
lib=(base/'lib.rs').read_bytes()+b"""
use aspis_core::field::QM31 as K;
impl K {pub fn from_le_bytes(_bytes:&[u8])->Option<Self>{unreachable!()}}
impl<'a> ResumeReader<'a> {
 pub fn e(&mut self)->Result<E,Error>{unreachable!()}
 fn raw<const N:usize>(&mut self)->[u8;N] {let b=self.bytes[self.at..self.at+N].try_into().unwrap();self.at+=N;b}
 pub fn k(&mut self)->Result<K,Error>{K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)}
}
pub struct ResumeHeader<'a>{pub r:ResumeReader<'a>,pub end:usize,pub state:[u8;32],pub roots:[[u8;32];2]}
pub fn begin_fields(header:ResumeHeader<'_>)->Result<ResumeBegin<'_>,Error>{
 let mut r=header.r;
"""+begin+b"""
 Ok(ResumeBegin{r,end:header.end,state:header.state,roots:header.roots,gamma,kappa,alpha})
}
pub fn semantic_fill(mut semantic_alpha:[K;10],mut r:ResumeReader<'_>)->Result<([K;10],ResumeReader<'_>),Error>{
"""+semantic[semantic.index(b'for x'):] +b"""
 Ok((semantic_alpha,r))
}
"""
outputs={'lib.rs':lib,'original-resume.rs':old}
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(base/n).read_bytes()
pins=json.loads((base/'source-pins.json').read_text())
info=dict(original_sha256=sha(old),begin_original_sha256=sha(begin),semantic_original_sha256=sha(semantic),scope='Exact four Reader.e source calls and exact ten-element mutable-array Reader.k source loop. Owning reader handbacks explicit, header/query/tail fragments remain common computations and receive no retained decoded values. No canonicality law premise.',opaque_paths=pins['opaque_paths']+['crate::_::e','crate::_::from_le_bytes'],roots=['crate::begin_fields','crate::semantic_fill'],kit_files={n:sha(b) for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(info,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,source=sha(lib),original=sha(old))))
