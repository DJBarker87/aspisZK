from pathlib import Path
import subprocess,json,hashlib,difflib,sys
E=Path(__file__).resolve().parent;R=E.parents[1];C='programs/r1-cost-probe/src/';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';width=int(sys.argv[1]);assert width in [32,2048,3717]
base=subprocess.check_output(['git','show',F+':'+C+'lib.rs'],cwd=R,text=True);assert 'hashv(parts).to_bytes()' in base
lib='#![cfg_attr(kani, feature(allocator_api))]\n'+base+'\n#[cfg(kani)] extern crate alloc;\n#[cfg(kani)] #[path="NFW_syscall.rs"] mod NFW_syscall;\n'
code='''use solana_program::hash::Hash;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log<'a>{reply:[u8;32],calls:usize,parts:Option<&'a[&'a[u8]]>}
// Frozen expression; only the runtime call is a local-record cut. The corrupt
// argument control changes the actual call argument, not the recording code.
fn syscall_cut<'a>(parts:&'a[&'a[u8]],log:&mut Log<'a>)->[u8;32]{let mut hashv=|xs:&'a[&'a[u8]]|{log.calls+=1;log.parts=Some(xs);Hash::new_from_array(log.reply)};hashv(if cfg!(NFW_badarg)&&!parts.is_empty(){&parts[1..]}else{parts}).to_bytes()}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn syscall_bytes(){
 const WIDTH:usize=NFW_WIDTH;
 let data:[[u8;WIDTH];5]=kani::any();let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(lengths[i]<=WIDTH);i+=1;}
 let count:usize=if cfg!(NFW_badarg)||cfg!(NFW_invert){1}else{kani::any()};kani::assume(count<=5);
 let parts:[&[u8];5]=[&data[0][..lengths[0]],&data[1][..lengths[1]],&data[2][..lengths[2]],&data[3][..lengths[3]],&data[4][..lengths[4]]];let input=&parts[..count];
 let mut log=Log{reply:kani::any(),calls:0,parts:None};let result=syscall_cut(input,&mut log);let word:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(word<32);
 assert_eq!(log.calls,1);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 let seen=log.parts.unwrap();let same=seen.len()==input.len()&&core::ptr::eq(seen,input);assert!(same);
 if same&&count>0{let part:usize=if cfg!(NFW_badarg){0}else{kani::any()};kani::assume(part<count);let at:usize=kani::any();let expected=if at<lengths[part]{data[part][at]}else{0};let actual=if at<seen[part].len(){seen[part][at]}else{0};assert_eq!(actual,expected);}
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_hash(){let src=Hash::new_from_array(kani::any());let mut dst=Hash::new_from_array(kani::any());unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<32);assert!((dst.to_bytes()[word]==src.to_bytes()[word])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn hash_value(){let reply:[u8;32]=kani::any();let value=Hash::new_from_array(reply).to_bytes();let word:usize=kani::any();kani::assume(word<32);assert!((value[word]==reply[word])!=cfg!(NFW_invert));}
'''.replace('NFW_WIDTH',str(width))
files={C+'lib.rs':lib,C+'NFW_syscall.rs':code};x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x.update(files);(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NFW_syscall.rs.txt').write_text(code)
patch=''.join(difflib.unified_diff(base.splitlines(True),lib.splitlines(True),fromfile='a/'+C+'lib.rs',tofile='b/'+C+'lib.rs'))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NFW_syscall.rs'));(E/'NFW_syscall.patch').write_text(patch)
(E/f'NFW_RUNTIME_DOMAIN_{width}.json').write_text(json.dumps(dict(width=width,parts='0..5 immutable byte slices, every byte arbitrary and every selected offset checked; empty parts/slices admitted',source_expression='hashv(parts).to_bytes()',scope='Bounded-domain packet only; larger checkpoint/proof-part and arbitrary-alias contexts are OPEN. No global digest row admitted.',controls=['reply inversion on a valid count1 witness','corrupt actual hashv argument by dropping its first part; recording code unchanged']),indent=1)+'\n')
