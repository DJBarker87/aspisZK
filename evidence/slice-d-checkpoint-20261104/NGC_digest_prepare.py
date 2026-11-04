from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());P='programs/r1-cost-probe/src/'
s=x[P+'lib.rs'];s=s.replace('//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.','//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.\n#[cfg(kani)] extern crate alloc;',1);s='#![cfg_attr(kani,feature(allocator_api))]\n'+s;s+='\n#[cfg(kani)]\n#[path="NGC_digest.rs"]\nmod NGC_digest;\n';x[P+'lib.rs']=s
x[P+'NGC_digest.rs']='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log<'a>{outer:*const &'a[u8],count:usize,index:usize,part:*const u8,length:usize,calls:u8,reply:[u8;32]}
fn hashv_window<'a>(parts:&[&'a[u8]],log:&mut Log<'a>)->solana_program::hash::Hash{
 log.outer=parts.as_ptr();log.count=parts.len();log.calls+=1;
 if log.index<parts.len(){log.part=parts[log.index].as_ptr();log.length=parts[log.index].len();}
 solana_program::hash::Hash::new_from_array(log.reply)
}
// Literal digest expression, with only its syscall boundary instrumented.
fn digest_window<'a>(parts:&[&'a[u8]],log:&mut Log<'a>)->[u8;32]{hashv_window(parts,log).to_bytes()}
#[kani::proof] KMXL
fn digest_forward(){let b0:[u8;57607]=kani::any();let b1:[u8;57607]=kani::any();let b2:[u8;57607]=kani::any();let n0:usize=kani::any();let n1:usize=kani::any();let n2:usize=kani::any();kani::assume(n0<=57607&&n1<=57607&&n2<=57607);let parts=[&b0[..n0],&b1[..n1],&b2[..n2]];let n:usize=kani::any();kani::assume(n<=3);let i:usize=kani::any();kani::assume(i<3);let reply:[u8;32]=kani::any();let mut log=Log{outer:core::ptr::null(),count:99,index:i,part:core::ptr::null(),length:99,calls:0,reply};let got=digest_window(&parts[..n],&mut log);assert!(log.calls==1&&log.outer==parts.as_ptr()&&log.count==n);if i<n{assert!(log.part==parts[i].as_ptr()&&log.length==parts[i].len());}assert!((got==reply)!=cfg!(NGC_invert));}
#[kani::proof] KMXL
fn digest_copy_positive(){let src:[u8;32]=kani::any();let h=solana_program::hash::Hash::new_from_array(src);let out=h.to_bytes();let i:usize=kani::any();kani::assume(i<32);assert!(out[i]==src[i]);}
#[kani::proof] KMXL
fn digest_copy_negative(){let src:[u8;32]=kani::any();let h=solana_program::hash::Hash::new_from_array(src);let out=h.to_bytes();let i:usize=kani::any();kani::assume(i<32);assert!(out[i]!=src[i]);}
'''.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]''')
(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
