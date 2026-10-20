#!/usr/bin/env python3
"""Extract frozen declarations verbatim; attach contracts only in an isolated tool."""
import argparse,hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'r22-overflow-kit'))
from prepare import fn
from inventory import blob,FREEZE
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=[]
def get(path,owner,attrs=''):
    body,line=fn(blob(path),owner)
    pins.append(dict(path=path,owner=owner,line=line,sha256=sha(body.encode()),body_edit='none',attributes=attrs))
    return attrs+'\n'+body+'\n'
F='crates/aspis-core/src/field.rs';V='crates/aspis-r1-cost-probe/src/verifier.rs'
s='''#![allow(dead_code)]
const P:u32=0x7fffffff;
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct M31(u32);
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct CM31 {a:M31,b:M31}
#[derive(Clone,Copy,Debug,kani::Arbitrary)] struct QM31 {c0:CM31,c1:CM31}
type K=QM31;
#[derive(Clone,Copy,Debug,kani::Arbitrary)] enum Error {Checkpoint}
fn cm_ok(x:CM31)->bool {x.a.0<P && x.b.0<P}
fn k_ok(x:K)->bool {cm_ok(x.c0)&&cm_ok(x.c1)}
'''
for ty,n,pred in [('M31',4,'x.0<P'),('CM31',8,'cm_ok(*x)'),('QM31',16,'k_ok(*x)')]:
    attrs=(f'#[kani::requires(bytes.len()=={n})]\n' if ty!='M31' else '')+f'#[kani::ensures(|r:&Option<{ty}>| r.as_ref().map_or(true, |x| {pred}))]'
    s+=f'impl {ty} {{\n'+get(F,ty+'::from_le_bytes',attrs)+'}\n'
    stubs='' if ty=='M31' else ('#[kani::stub_verified(M31::from_le_bytes)]\n' if ty=='CM31' else '#[kani::stub_verified(CM31::from_le_bytes)]\n')
    arg='b' if ty=='M31' else '&b'
    s+=f'#[kani::proof_for_contract({ty}::from_le_bytes)]\n{stubs}fn decoder_{ty.lower()}() {{let b:[u8;{n}]=kani::any(); {ty}::from_le_bytes({arg});}}\n'
s+='''struct Reader<'a>{bytes:&'a[u8],at:usize}
impl Reader<'_> {
'''
s+=get(V,"Reader<'a>::raw",'''#[kani::requires(N<=32 && self.bytes.len()<=4880 && N<=self.bytes.len() && self.at<=self.bytes.len()-N)]
#[kani::modifies(&mut self.at)]
#[kani::ensures(|_r:&[u8;N]| self.at==old(self.at)+N && self.at<=self.bytes.len())]''')
s+=get(V,"Reader<'a>::k",'''#[kani::requires(self.bytes.len()<=4880 && self.bytes.len()>=16 && self.at<=self.bytes.len()-16)]
#[kani::modifies(&mut self.at)]
#[kani::ensures(|r:&Result<K,Error>| self.at==old(self.at)+16 && r.as_ref().map_or(true, |x| k_ok(*x)))]''')
s+='}\n'
for n in [4,16,32]:
    s+=f'''#[kani::proof_for_contract(Reader::raw::<{n}>)] #[kani::unwind(34)]
fn reader_raw{n}() {{let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880); let mut r=Reader{{bytes:&b[..len],at:kani::any()}}; r.raw::<{n}>();}}
'''
s+='''#[kani::proof_for_contract(Reader::k)]
#[kani::stub_verified(Reader::raw::<16>)] #[kani::stub_verified(QM31::from_le_bytes)]
fn reader_k() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880);let mut r=Reader{bytes:&b[..len],at:kani::any()};r.k();}
'''
s+=get(V,'read_checkpoint_semantic_alpha', '''#[kani::requires(bytes.len()<=4880 && bytes.len()>=160 && at<=bytes.len()-160)]
#[kani::ensures(|r:&Result<([K;10],usize),Error>| r.as_ref().map_or(true, |(ks,end)| *end==at+160 && k_ok(ks[0]) && k_ok(ks[1]) && k_ok(ks[2]) && k_ok(ks[3]) && k_ok(ks[4]) && k_ok(ks[5]) && k_ok(ks[6]) && k_ok(ks[7]) && k_ok(ks[8]) && k_ok(ks[9])))]''')
s+='''#[kani::proof_for_contract(read_checkpoint_semantic_alpha)] #[kani::unwind(12)]
#[kani::stub_verified(Reader::k)]
fn semantic_alpha() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880);read_checkpoint_semantic_alpha(&b[..len],kani::any());}
'''
s+=get(V,'read_checkpoint_weights','''#[kani::requires(bytes.len()<=4880 && weights.len()<=256 && 16*weights.len()<=bytes.len() && at<=bytes.len()-16*weights.len())]
#[kani::ensures(|r:&Result<(Vec<K>,usize),Error>| r.as_ref().map_or(true, |(ks,end)| ks.len()==old(weights.len()) && *end==at+16*ks.len() && ks.iter().all(|x| k_ok(*x))))]''')
s+='''#[kani::proof_for_contract(read_checkpoint_weights)] #[kani::unwind(258)]
#[kani::stub_verified(Reader::k)]
fn checkpoint_weights256() {let b:[u8;4880]=kani::any(); let w=kani::vec::any_vec::<K,256>(); let len:usize=kani::any();kani::assume(len<=4880);read_checkpoint_weights(&b[..len],kani::any(),w);}
'''
# One exact iterator body, lifted to a function contract (reference reborrows only).
s+="""#[kani::requires(bytes.len()<=4880 && bytes.len()>=16 && *at<=bytes.len()-16)]
#[kani::modifies(at,out)]
#[kani::ensures(|r:&Result<(),Error>| r.is_err() || (*at==old(*at)+16 && k_ok(*out)))]
fn read_one_weight(bytes:&[u8],at:&mut usize,out:&mut K)->Result<(),Error> {
    let mut reader=Reader{bytes,at:*at};
    let value=reader.k()?;
    *at=reader.at;
    *out=value;
    Ok(())
}
#[kani::proof_for_contract(read_one_weight)]
#[kani::stub_verified(Reader::k)]
fn weight_body() {let b:[u8;4880]=kani::any();let len:usize=kani::any();kani::assume(len<=4880);let mut at=kani::any();let mut out=kani::any();read_one_weight(&b[..len],&mut at,&mut out);}
"""
# Validate the lift against the exact original body. Not a source-language equivalence theorem.
wbody=fn(blob(V),'read_checkpoint_weights')[0]
assert 'let mut reader=Reader{bytes,at};' in wbody and 'let value=reader.k()?;' in wbody and 'at=reader.at;' in wbody and '*out=value;' in wbody
pins.append(dict(path=V,owner='read_checkpoint_weights::iteration',body_edit='lift four statements into read_one_weight; at:*at and *at=reader.at, plus Ok(()); preserves early error and write order',sha256=sha(wbody.encode())))

# Exact numerical row, with actual four correlated limb products, unlike pass one.
s+=get(V,'residue_limb_at')+get(V,'power_limb_at')
s+='''const B:u64=1<<34;
const C:u64=(P as u64-1)*(P as u64-1);
fn row_bound(row:&[u64;4],limit:u64)->bool {row.iter().all(|x|*x<limit)}
'''
s+=get(V,'update_residue_row','''#[kani::requires(k_ok(power) && basis.0<P)]
#[kani::requires(row_bound(row,if flush {B+3*C} else {B+2*C}))]
#[kani::modifies(row)]
#[kani::ensures(|_:&()| row_bound(row,if flush {B} else {B+3*C}))]''')
s+='''#[kani::proof_for_contract(update_residue_row)] #[kani::unwind(6)]
fn residue_row() {let mut row=kani::any();update_residue_row(&mut row,kani::any(),kani::any(),kani::any());}
'''
s=s.replace('for limb in row {', 'for limb in &mut *row {')
pins[-1]['body_edit']='for limb in row -> for limb in &mut *row: explicit reborrow required by Kani contract macro; identical iter_mut traversal'
files={'lib.rs':s,'Cargo.toml':'''[package]
name="r22-overflow2-contracts"
version="0.1.0"
edition="2021"
[lib]
path="lib.rs"
[workspace]
[profile.dev]
opt-level=3
overflow-checks=true
debug=false
[profile.release]
opt-level=3
overflow-checks=true
'''}
manifest=dict(source_revision=FREEZE,declarations=pins,generated={k:sha(v.encode()) for k,v in files.items()},context='Exact copied bodies, source-shaped field structs and Error::Checkpoint only. Contracts are added attributes; no shipped edits. This is not a Charon/Aeneas or ELF refinement proof. Finite harness extents are recorded separately; contract syntax is not universal proof evidence.')
files['source-pins.json']=json.dumps(manifest,indent=2)+'\n'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
for name,body in files.items():
    dest=HERE/'generated'/name
    if args.check:assert dest.read_text()==body,name
    else:dest.parent.mkdir(exist_ok=True);dest.write_text(body)
print(json.dumps({'source_revision':FREEZE,'declarations':len(pins),'files':len(files)}))
