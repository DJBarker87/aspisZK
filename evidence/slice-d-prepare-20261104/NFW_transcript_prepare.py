from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-r1-cost-probe/src/';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
base=subprocess.check_output(['git','show',F+':'+C+'transcript.rs'],cwd=R,text=True)
text=base+'\n#[cfg(kani)]\n#[path="NFW_transcript.rs"]\nmod NFW_transcript;\n'
code='''use super::*;
use core::cell::RefCell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log {calls:usize,counts:[usize;3],lens:[[usize;4];3],bytes:[[u8;4];3],at:[[usize;4];3],replies:[[u8;32];3]}
#[derive(Clone,Copy)]struct Hash<'a>(&'a RefCell<Log>);
impl Digest32 for Hash<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{
 let mut l=self.0.borrow_mut();let k=l.calls;assert!(k<3);assert!(parts.len()<=4);
 l.counts[k]=parts.len();let mut j=0;while j<parts.len(){l.lens[k][j]=parts[j].len();let pos=l.at[k][j];l.bytes[k][j]=if pos<parts[j].len(){parts[j][pos]}else{0};j+=1;}
 l.calls+=1;l.replies[k]
}}
fn log()->RefCell<Log>{RefCell::new(Log{calls:0,counts:[0;3],lens:[[0;4];3],bytes:[[0;4];3],at:kani::any(),replies:kani::any()})}
fn byte(s:&[u8],at:usize)->u8{if at<s.len(){s[at]}else{0}}
fn observed(l:&Log,k:usize,j:usize,s:&[u8]){assert_eq!(l.lens[k][j],s.len());assert_eq!(l.bytes[k][j],byte(s,l.at[k][j]));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn new_seed(){
 let state:[u8;32]=kani::any();let l=log();let t=Transcript::new(Hash(&l),state,Variant::S2);
 let word:usize=kani::any();kani::assume(word<32);let l=l.borrow();assert_eq!(l.calls,1);assert_eq!(l.counts[0],3);
 observed(&l,0,0,b"UNPROVED:R1:PRIVATE-SALTED:P3");observed(&l,0,1,&[2]);observed(&l,0,2,&state);
 assert!((t.state[word]==l.replies[0][word])!=cfg!(NFW_invert));
}
fn run_absorb<const N:usize>(block:bool){
 let state:[u8;32]=kani::any();let payload:[u8;N]=kani::any();let len:usize=kani::any();kani::assume(len<=N);
 let row:u8=kani::any();kani::assume(row<=95);let word:usize=kani::any();kani::assume(word<32);
 let l=log();let mut t=Transcript{state,hash:Hash(&l)};
 if block {
  let reply=t.block(row,&payload[..len]);let l=l.borrow();
  assert_eq!(l.calls,3);assert_eq!(l.counts[0],4);assert_eq!(l.counts[1],2);assert_eq!(l.counts[2],2);
  observed(&l,0,0,&state);observed(&l,0,1,&[0,160+row]);observed(&l,0,2,&(len as u32).to_le_bytes());observed(&l,0,3,&payload[..len]);
  observed(&l,1,0,&l.replies[0]);observed(&l,1,1,&[1]);observed(&l,2,0,&l.replies[0]);observed(&l,2,1,&[2]);
  assert_eq!(reply[word],l.replies[1][word]);assert!((t.state[word]==l.replies[2][word])!=cfg!(NFW_invert));
 } else {
  t.absorb(row,&payload[..len]);let l=l.borrow();assert_eq!(l.calls,1);assert_eq!(l.counts[0],4);
  observed(&l,0,0,&state);observed(&l,0,1,&[0,160+row]);observed(&l,0,2,&(len as u32).to_le_bytes());observed(&l,0,3,&payload[..len]);
  assert!((t.state[word]==l.replies[0][word])!=cfg!(NFW_invert));
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn absorb_window(){run_absorb::<2048>(false);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn block_window(){run_absorb::<2048>(true);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_digest(){let src:[u8;32]=kani::any();let mut dst:[u8;32]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<32);assert!((dst[word]==src[word])!=cfg!(NFW_invert));}
'''
(E/'NFW_transcript.rs.txt').write_text(code)
x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x.update({C+'transcript.rs':text,C+'NFW_transcript.rs':code});(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x.update({C+'transcript.rs':hashlib.sha256(text.encode()).hexdigest(),C+'NFW_transcript.rs':hashlib.sha256(code.encode()).hexdigest()});(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
patch=''.join(difflib.unified_diff(base.splitlines(True),text.splitlines(True),fromfile='a/'+C+'transcript.rs',tofile='b/'+C+'transcript.rs'))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NFW_transcript.rs'))
(E/'NFW_transcript.patch').write_text(patch)
