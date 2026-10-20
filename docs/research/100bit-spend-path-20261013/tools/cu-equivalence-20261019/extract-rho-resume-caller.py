#!/usr/bin/env python3
"""Factor unchanged resume at its two canonical scalar reads and weight loop."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];out=tool/'rho-resume-caller-input';sha=lambda b:hashlib.sha256(b).hexdigest()
revs=['a29133e2508d2f50a80e68d589259f2ba397da0e','16a39d2a8a5124e25c787f2b9fcaf8449fb84611','39c2971dd16c95858a4cfd2c9ae35da052eacfa9'];path='crates/aspis-r1-cost-probe/src/verifier.rs'
def item(src,start):
 at=src.index(start);j=src.index(b'{',at);depth=1;k=j+1
 while depth:
  if src[k:k+1]==b'{':depth+=1
  elif src[k:k+1]==b'}':depth-=1
  k+=1
 return src[at:k]
originals=[item(subprocess.check_output(['git','-C',str(repo),'show',r+':'+path]),b'pub fn resume<') for r in revs];assert originals[0]==originals[1]==originals[2];original=originals[0]
# Exact source block boundaries. Values rho and power are never passed to
# common computations after their source decoder produces them.
start=original.index(b'{')+1
rho=original.index(b'let rho=r.k()?;');middle=rho+len(b'let rho=r.k()?;')
power=original.index(b'let power=r.k()?;');allocate=power+len(b'let power=r.k()?;')
loop=original.index(b'    for x in &mut weights');after=original.index(b'    if r.at!=end')
fragments={'begin.rs':original[start:rho],'middle.rs':original[middle:power],'allocate.rs':original[allocate:loop],'weights.rs':original[loop:after],'tail.rs':original[after:]}
assert b''.join([fragments['begin.rs'],b'let rho=r.k()?;',fragments['middle.rs'],b'let power=r.k()?;',fragments['allocate.rs'],fragments['weights.rs'],fragments['tail.rs']])==original[start:]
lib=(tool/'rho-query-context-input/lib.rs').read_bytes()
lib+=b'''\nuse alloc::{boxed::Box,vec::Vec};
#[derive(Clone)]
pub struct ResumeReader<'a> {pub bytes:&'a[u8],pub at:usize}
pub struct ResumeBegin<'a>{pub r:ResumeReader<'a>,pub end:usize,pub state:[u8;32],pub roots:[[u8;32];2],pub gamma:E,pub kappa:E,pub alpha:[E;2]}
pub struct ResumeMiddle<'a>{pub r:ResumeReader<'a>,pub queries:[u32;22],pub semantic_alpha:[aspis_core::field::QM31;10],pub z:[aspis_core::circle::SecureCirclePoint;2],pub claim:E,pub rhs:E}
pub fn source_resume_begin<'a,H:Digest32>(_bytes:&'a[u8],_proof:&[u8],_public:&[u8],_v:transport::Variant,_hash:H)->Result<ResumeBegin<'a>,Error>{unreachable!()}
pub fn source_resume_middle<'a>(_r:ResumeReader<'a>)->Result<ResumeMiddle<'a>,Error>{unreachable!()}
pub fn source_resume_allocate(_v:transport::Variant)->Result<Vec<aspis_core::field::QM31>,Error>{unreachable!()}
pub fn source_read_k<'a>(_r:ResumeReader<'a>)->Result<(aspis_core::field::QM31,ResumeReader<'a>),Error>{unreachable!()}
pub fn source_resume_weights<'a>(_weights:Vec<aspis_core::field::QM31>,_r:ResumeReader<'a>)->Result<(Vec<aspis_core::field::QM31>,ResumeReader<'a>),Error>{unreachable!()}
pub fn source_resume_caller<H:Digest32>(bytes:&[u8],proof:&[u8],public:&[u8],v:transport::Variant,hash:H)->Result<(Box<Prepared>,Accumulator),Error>{
 let begin=source_resume_begin(bytes,proof,public,v,hash)?;
 let (rho,r)=source_read_k(begin.r)?;
 let middle=source_resume_middle(r)?;
 let (power,r)=source_read_k(middle.r)?;
 let weights=source_resume_allocate(v)?;
 let (weights,r)=source_resume_weights(weights,r)?;
 if r.at!=begin.end {return Err(Error::Checkpoint);}
 Ok((Box::new(Prepared{variant:v,roots:begin.roots,gamma:begin.gamma,kappa:begin.kappa,alpha:begin.alpha,rho,queries:middle.queries,semantic_alpha:middle.semantic_alpha,z:middle.z,claim:middle.claim,state:begin.state}),Accumulator{weights,rhs:middle.rhs,power,next:bytes[9] as usize}))
}
'''
outputs={'lib.rs':lib,'fragments/original-resume.rs':original}
for n,b in fragments.items():outputs['fragments/'+n]=b
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(tool/'rho-query-context-input'/n).read_bytes()
base=json.loads((tool/'rho-query-context-input/source-pins.json').read_text())
pins=dict(revisions=revs,source_path=path,original_sha256=sha(original),fragment_reassembly_checked=True,scope='Unchanged complete resume factored at exact source read/weight-loop boundaries. Private Reader handbacks made explicit. Common computations receive neither stored rho nor power and cannot mutate them. Tail check and complete Prepared/Accumulator construction retained. No header-bound premise needed by the checked stage theorem.',opaque_paths=base['opaque_paths']+['crate::source_resume_begin','crate::source_resume_middle','crate::source_resume_allocate','crate::source_read_k','crate::source_resume_weights'],roots=['crate::source_resume_caller'],kit_files={n:sha(b) for n,b in outputs.items()})
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'lib':sha(lib),'original':sha(original)}))
