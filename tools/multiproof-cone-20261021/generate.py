#!/usr/bin/env python3
"""Exact frozen source cuts; --check validates every byte and substitution."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2]; T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021'
pins=json.loads((E/'source-pins.json').read_text())['files']
for p,v in pins.items(): assert hashlib.sha256((R/p).read_bytes()).hexdigest()==v['sha256'],p
cuts=[]
def item(path,marker):
 s=(R/path).read_text();a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 body=s[a:e];cuts.append(dict(path=path,marker=marker,sha256=hashlib.sha256(body.encode()).hexdigest(),body=body));return body
base='crates/aspis-r1-cost-probe/src/'
mp=(R/(base+'multiproof.rs')).read_text().split('/// Prover side:')[0]
# The whole verifier prefix is copied, including well_formed and all callees.
# Expose private helpers only to this proof crate's sibling harness module.
mp=mp.replace('fn well_formed(', 'pub(crate) fn well_formed(')
wire=item(base+'r1_wire.rs','pub const fn row_shape(')
compact=(R/(base+'compact.rs')).read_text().split('#[cfg(test)]')[0]
compact=compact.replace('crate::verifier::SEMANTIC_BYTES','13_831')
# Batch primitives, verbatim; leaf hashing itself remains a separate byte cut.
markers=['fn batch_keys(','fn sort_batch_keys(','fn batch_leaf<','fn same_batch_leaf(','fn same_batch_index(','fn batch_key_at(']
batch='\n'.join(item(base+'candidate.rs',m).replace('fn ','pub(crate) fn ',1) for m in markers)
# Exact inner iteration of the frozen insertion sort; avoid whole-prefix BMC.
sort_body=next(c['body'] for c in cuts if c['marker']=='fn sort_batch_keys(')
sa=sort_body.index('        let mut j = i;')
sb=sort_body.rfind('\n    }')
sort_loop=sort_body[sa:sb]
assert sort_loop.endswith('        }')
sort_loop=sort_loop[:-len('        }')]+'            (true,keys,j)\n        } else {(false,keys,j)}'
sort_loop=sort_loop.replace('while j > 0','if j > 0',1)
sort_step='pub(crate) fn sort_insert_step(mut keys:[u64;multiproof::MAX_BATCH],i:usize)->(bool,[u64;multiproof::MAX_BATCH],usize) {\n'+sort_loop+'\n}\n'

# The binary group is the exact source match arm plus its chronological writes.
a=mp.index('                    if i + 1 < n');b=mp.index('\n                Arity::Eight =>',a)
arm=mp[a:b];arm=arm[:arm.rfind('\n                }')]
step='''pub(crate) fn binary_group<H:Digest32>(hash:H,idx:&mut [u32;16],val:&mut [[u8;32];16],n:usize,nodes:&[u8],at:&mut usize,w:&mut usize,i:&mut usize)->bool {
 let parent=index_at(idx,*i)>>1;
 let digest={
'''+arm.replace('i +','*i +').replace('i)','*i)').replace('i,','*i,').replace('**i +=','*i +=').replace('at..at + 32','*at..*at + 32').replace('at +=','*at +=')+'''
 };
 idx[*w]=parent;val[*w]=digest;*w+=1;true
}
'''
# One exact outer iteration of verify_in_place, fixed to binary arity.
va=mp.index('        let mut w = 0;',mp.index('pub fn verify_in_place'))
vb=mp.index('        n = w;',va)+len('        n = w;')
level_body=mp[va:vb].replace('while i < n {','while i < *n {').replace('i + 1 < n','i + 1 < *n').replace('i < n &&','i < *n &&').replace('at..at + 32','*at..*at + 32').replace('at +=','*at +=').replace('n = w;','*n = w;')
level='pub(crate) fn binary_level<H:Digest32>(hash:H,idx:&mut [u32;16],val:&mut [[u8;32];16],n:&mut usize,nodes:&[u8],at:&mut usize)->bool {\nlet arity=Arity::Two;\n'+level_body+'\ntrue\n}\n'

# Exact count-level group; arity is fixed to Two by the concrete caller.
a=mp.index('            let parent = index_at(&level, i) >> arity.bits();')
b=mp.index('            i = j;',a)+len('            i = j;')
count_group="pub(crate) fn count_group(level:&mut [u32;16],n:usize,mut i:usize,mut w:usize)->(usize,usize,usize) {\n let arity=Arity::Two;let mut count=0;\n"+mp[a:b].replace('index_at(&level,','index_at(level,')+"\n(i,w,count)\n}\n"
# Candidate insertion body is copied from the source after batch_leaf, ending before node_count.
s=(R/(base+'candidate.rs')).read_text();a=s.index('        if d > 0 && same_batch_index');b=s.index('\n    let count = multiproof::node_count',a)
leaf=s[a:b];leaf=leaf[:leaf.rfind('\n    }')]
leaf=leaf.replace('return Err(Error::Merkle);','return false;').replace('            continue;','            return true;')
leaf=leaf.replace('d >','*d >').replace('d -','*d -').replace('idx[d]','idx[*d]').replace('val[d]','val[*d]').replace('d +=','*d +=')
leaf='''pub(crate) fn leaf_insert(idx:&mut [u32;16],val:&mut [[u8;32];16],d:&mut usize,index:u32,leaf:[u8;32])->bool {
'''+leaf+'\ntrue\n}\n'
# The entire key-position/leaf iteration, including duplicate-error chronology.
la=s.index('        let key = batch_key_at(&keys, key_position);')
lb=s.index('\n    let count = multiproof::node_count',la)
leaf_body=s[la:lb];leaf_body=leaf_body[:leaf_body.rfind('\n    }')]
leaf_body=leaf_body.replace('let q = opening(proof, lo + (key & 0xff) as usize);','let selected = lo + (key & 0xff) as usize;')
leaf_body=leaf_body.replace('let leaf = batch_leaf(hash, tree, q);','let observation = crate::adoption::leaf_hash(tree,q,answer,coordinate);\n        let leaf = observation.digest;')
leaf_body=leaf_body.replace('return Err(Error::Merkle);','return (false,key_position,selected,observation.calls,observation.event);').replace('            continue;','            return (true,key_position,selected,observation.calls,observation.event);')
leaf_body=leaf_body.replace('d >','*d >').replace('d -','*d -').replace('idx[d]','idx[*d]').replace('val[d]','val[*d]').replace('d +=','*d +=')
leaf_iteration='#[cfg(kani)]\npub(crate) fn leaf_batch_iteration(keys:[u64;16],mut key_position:usize,lo:usize,tree:usize,q:&[u8;832],idx:&mut [u32;16],val:&mut [[u8;32];16],d:&mut usize,answer:[u8;32],coordinate:usize)->(bool,usize,usize,usize,u8) {\n'+leaf_body+'\n(true,key_position,selected,observation.calls,observation.event)\n}\n'

# Exact parser/semantic functions and source expansion pipeline.
wire_items=[item(base+'r1_wire.rs',m) for m in ['pub enum Error {','fn validate_record_fields(','pub fn parse_record(','pub struct Prefix<',"fn parse_record_at<'a>",'pub fn parse(bytes:','pub fn record(&self,']]
wire_more='#[derive(Debug)]\n'+'\n'.join(wire_items[:5]).replace('fn validate_record_fields(', 'pub(crate) fn validate_record_fields(')+"\nimpl<'a> Prefix<'a> {\n"+'\n'.join(wire_items[5:])+"\n}\n"
parser_items=[item(base+'candidate.rs',m) for m in ['fn opening(','pub fn parse_shape(','fn canonical_scan(']]
echeck=item(base+'verifier.rs','fn echeck(')
parser='pub mod parser {\n use super::compact::{self,CodecError,OPENING};\n use aspis_core::field::{M31,QM31 as K,WideExact as E};\n #[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum Variant {S2}\n impl Variant {fn tag(self)->u8 {2}}\n #[derive(Debug)] pub enum Error {Parse}\n impl From<CodecError> for Error {fn from(_:CodecError)->Self{Self::Parse}}\n'+echeck+'\n'+'\n'.join(x.replace('fn canonical_scan(', 'pub(crate) fn canonical_scan(') for x in parser_items)+'\n}\n'
outputs={T/'src/frozen.rs':'''// Generated by generate.py; no production dependency on this crate.
pub mod r1_wire {const CLAIMS:usize=87;const LANES:usize=29;\nuse aspis_core::field::{WideExact,QM31};\n
'''+wire+'\n'+wire_more+'''
}
pub mod compact {
'''+compact+'''
}
pub mod multiproof {
'''+mp+'\n'+step+'\n'+level+'\n'+count_group+'''
}
pub mod batch {
use super::multiproof;
use aspis_core::{r0::merkle,Digest32};
use aspis_core::state_only_private_merkle::private_leaf_hash_with_digest;
'''+batch+'\n'+sort_step+'\n'+leaf+'\n'+leaf_iteration+'\n}\n'+parser}
ledger=dict(schema='frozen-parser-multiproof-cuts-v1',exact_items=cuts,substitutions=[
 'compact.rs: verifier::SEMANTIC_BYTES replaced by its pinned literal 13_831',
 'multiproof verifier prefix: private well_formed exposed pub(crate)',
 'batch helpers: private functions exposed pub(crate)',
 'sort atomic step: exact let-j/while guard and swap/decrement body; while becomes one if; return continuation flag, owned keys and cursor',
 'adoption_level: factor each exact binary_group body into the separately verified source_row wrapper; same i<n guard, chronological scratch/cursor update and n=w; return oracle ordinal/coordinate observation and use arbitrary independent per-call replies',
 'binary_level: exact verify_in_place outer level body; fix Arity::Two, n/at become scalar references, success returns true, rejection scratch and local n retained',
 'leaf_batch_iteration: exact candidate batch_tree key/read/hash/duplicate/write iteration; pass the selected opening as q and return its selected ordinal, cursor, event and count; hash replaced only by its separately verified observer wrapper; error/continue become the corresponding bool and poststate',
 'node-count group: fix Arity::Two; index_at(&level,...) becomes index_at(level,...) for the mutable-reference wrapper; exact parent/group/write/increment order',
 'binary group: extract Two match arm; i/at/w become mutable scalar references; false return preserved; exact parent/write order retained',
 'wire validate_record_fields: expose pub(crate) in the proof copy; body unchanged',
 'wire Error: add Debug derive for proof-crate test diagnostics only',
 'parser: isolated Error/Variant carriers retain Parse and tag=2; wire validation and Prefix functions copied verbatim',
 'leaf insertion: d becomes scalar reference; Merkle error becomes false and continue becomes true; exact writes retained'],
 whole_prefixes={p:hashlib.sha256((R/(base+p)).read_bytes()).hexdigest() for p in ['compact.rs','multiproof.rs']},
 outputs={str(p.relative_to(R)):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()})
outputs[T/'src/adoption_level.rs']='// Generated by generate.py from the frozen binary level control.\n/// Same while guard, row call, chronological writes and n=w as the generated\n/// binary_level. source_row contains that exact row body and has a verified\n/// full-state contract; no arbitrary-coordinate weakening enters the stub.\npub fn source_level_via_rows(mut s:r::Scratch,nodes:&[u8],answers:&[[u8;32];16],selected:usize,coordinate:usize)->(bool,r::Scratch,usize,u8) {\n let mut i=0;let mut w=0;let mut calls=0;let mut event=0;\n while i<s.n {\n  assert!(calls<16);\n  let out=source_row(s,nodes,i,w,answers[calls],coordinate);\n  if calls==selected && out.calls>0 {event=out.event;}\n  calls+=out.calls;s=out.state;\n  if !out.success {return (false,s,calls,event);}\n  i=out.i;w=out.w;\n }\n s.n=w;(true,s,calls,event)\n}\n'
ledger['outputs'][str((T/'src/adoption_level.rs').relative_to(R))]=hashlib.sha256(outputs[T/'src/adoption_level.rs'].encode()).hexdigest()
outputs[E/'source-cuts.json']=json.dumps(ledger,indent=2)+'\n'
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print('Frozen cuts verified' if '--check' in sys.argv else 'Frozen cuts generated')
