from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent; R=P.parents[1]; cuts=[]
def item(path,marker):
 s=(R/path).read_text(); a=s.index(marker); b=s.index('{',a); d=1; e=b+1
 while d: d+=(s[e]=='{')-(s[e]=='}'); e+=1
 t=s[a:e]; cuts.append(dict(path=path,marker=marker,sha256=hashlib.sha256(t.encode()).hexdigest(),body=t)); return t
base='crates/aspis-r1-cost-probe/src/'
trait=item('crates/aspis-core/src/digest.rs','pub trait Digest32: Copy')
leaf=item('crates/aspis-core/src/state_only_private_merkle.rs','pub fn private_leaf_hash_with_digest<')
parent=item('crates/aspis-core/src/r0/merkle.rs','pub fn parent_with_digest<')
compact=(R/(base+'compact.rs')).read_text(); a=compact.index('pub const MAGIC:'); b=compact.index('#[derive(',a)
compact=compact[a:b].replace('crate::verifier::SEMANTIC_BYTES','13_831')
mp=(R/(base+'multiproof.rs')).read_text().split('/// Prover side:')[0]
# Preserve verifier prefix including all helpers; remove only module doc lines.
mp='\n'.join(l for l in mp.splitlines() if not l.startswith('//!'))
markers=['fn opening(','fn slot(','fn batch_keys(','fn sort_batch_keys(','fn batch_leaf<','fn same_batch_leaf(','fn same_batch_index(','fn batch_key_at(','fn batch_merkle_values<','fn batch_tree<']
batch='\n'.join(item(base+'candidate.rs',m).replace('fn ','pub(crate) fn ',1) for m in markers)
tree_body=next(c['body'] for c in cuts if c['marker']=='fn batch_tree<')
a=tree_body.index('        let key ='); b=tree_body.index('    let count =')
step=tree_body[a:b]; step=step[:step.rfind('    }')]
step=step.replace('let q = opening(proof, lo + (key & 0xff) as usize);','let selected = lo + (key & 0xff) as usize;')
step=step.replace('return Err(Error::Merkle);','return (false,key_position,selected,d);').replace('            continue;','            return (true,key_position,selected,d);')
step='pub(crate) fn leaf_step<H:Digest32>(keys:[u64;16],mut key_position:usize,lo:usize,tree:usize,q:&[u8],idx:&mut [u32;16],val:&mut [[u8;32];16],mut d:usize,hash:H)->(bool,usize,usize,usize) {\n'+step+'\n(true,key_position,selected,d)\n}\n'
batch+='\n'+step
source='''// Generated exact source cuts; BEl_generate.py --check verifies provenance.
extern crate alloc;
extern crate self as aspis_core;
pub type Digest = [u8;32];
'''+trait+'''
pub mod r0 { pub mod merkle {
use crate::{Digest,Digest32};
pub const C1_TAG:u8=0x71; pub const C2_TAG:u8=0xf1;
'''+parent+'''\n} }
pub const STATE_ONLY_PRIVATE_LEAF_SALT_BYTES:usize=32;
pub const DOM_LEAF:u8=0x10;
'''+leaf+'''
pub mod state_only_private_merkle {pub use crate::private_leaf_hash_with_digest;}
pub mod compact {
'''+compact+'''\n}
pub mod multiproof {
'''+mp+'''\n}
pub mod shipped {
use crate::{Digest32,compact::{self,OPENING,SPLIT,SLOT_NODES},multiproof::{self,Arity}};
use crate::{r0::merkle,private_leaf_hash_with_digest};
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum Error {Merkle,Parse}
'''+batch+'''\n}
'''
outputs={P/'BEl_rust/src/BEl_frozen.rs':source}
manifest={'exact_items':cuts,'full_prefixes':{base+'multiproof.rs':hashlib.sha256((R/(base+'multiproof.rs')).read_bytes()).hexdigest()},'substitutions':['Visibility only: batch helpers pub(crate).','compact LOGICAL_SEMANTIC replaced with pinned literal 13831; copied constants and slot_offset body.','Exact minimal Digest32, private leaf hash and eight-child hash bodies; imports re-exported through proof crate alias.','Proof crate Error has exactly reachable batch errors Merkle/Parse; no other variants used in copied body.','Module documentation omitted from multiproof prefix; body bytes retained.','leaf_step: exact while iteration, preselected q replaces opening range; key_position/d passed as locals; Err/continue mapped to explicit bool and poststate; no leaf/helper stubs.'],'outputs':{str(p.relative_to(P)):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()}}
outputs[P/'BEl_source_cuts.json']=json.dumps(manifest,indent=2)+'\n'
for p,s in outputs.items():
 if '--check' in sys.argv: assert p.read_text()==s,p
 else: p.write_text(s)
print('BEl exact cuts verified' if '--check' in sys.argv else 'BEl exact cuts generated')
