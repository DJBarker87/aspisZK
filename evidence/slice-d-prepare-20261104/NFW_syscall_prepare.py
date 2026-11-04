from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];C='programs/r1-cost-probe/src/';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
base=subprocess.check_output(['git','show',F+':'+C+'lib.rs'],cwd=R,text=True)
assert 'hashv(parts).to_bytes()' in base
text='#![cfg_attr(kani, feature(allocator_api))]\n'+base+'\n#[cfg(kani)] extern crate alloc;\n#[cfg(kani)] #[path="NFW_syscall.rs"] mod NFW_syscall;\n'
code='''use solana_program::hash::Hash;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log {reply:[u8;32],calls:usize,count:usize,lengths:[usize;5],bytes:[u8;5],positions:[usize;5]}
// Exact frozen wrapper expression, with only the runtime hashv call cut to an
// explicit local record. SHA values remain the accepted runtime trust row.
fn syscall_cut(parts:&[&[u8]],log:&mut Log)->[u8;32]{
 let mut hashv=|xs:&[&[u8]]|{log.calls+=1;log.count=xs.len();let mut i=0;while i<xs.len(){log.lengths[i]=xs[i].len();let j=log.positions[i];log.bytes[i]=if j<xs[i].len(){xs[i][j]}else{0};i+=1;}Hash::new_from_array(log.reply)};
 hashv(parts).to_bytes()
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn syscall_bytes(){
 let data:[[u8;57607];5]=kani::any();let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(lengths[i]<=57607);i+=1;}
 let count:usize=kani::any();kani::assume(count<=5);
 let parts:[&[u8];5]=[&data[0][..lengths[0]],&data[1][..lengths[1]],&data[2][..lengths[2]],&data[3][..lengths[3]],&data[4][..lengths[4]]];
 let mut log=Log{reply:kani::any(),calls:0,count:0,lengths:[0;5],bytes:[0;5],positions:kani::any()};
 let result=syscall_cut(&parts[..count],&mut log);let word:usize=kani::any();kani::assume(word<32);
 assert_eq!(log.calls,1);assert_eq!(log.count,count);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 let part:usize=kani::any();kani::assume(part<count);assert_eq!(log.lengths[part],lengths[part]);let at=log.positions[part];
 let expected=if at<lengths[part]{data[part][at]}else{0};assert!((log.bytes[part]==expected)!=cfg!(NFW_badarg));
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_hash(){let src=Hash::new_from_array(kani::any());let mut dst=Hash::new_from_array(kani::any());unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<32);assert!((dst.to_bytes()[word]==src.to_bytes()[word])!=cfg!(NFW_invert));}
'''
(E/'NFW_syscall.rs.txt').write_text(code)
x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x.update({C+'lib.rs':text,C+'NFW_syscall.rs':code});(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x.update({C+'lib.rs':hashlib.sha256(text.encode()).hexdigest(),C+'NFW_syscall.rs':hashlib.sha256(code.encode()).hexdigest()});(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
patch=''.join(difflib.unified_diff(base.splitlines(True),text.splitlines(True),fromfile='a/'+C+'lib.rs',tofile='b/'+C+'lib.rs'))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NFW_syscall.rs'))
(E/'NFW_syscall.patch').write_text(patch)
p=E/'NFW_run.py';s=p.read_text();needle="if os.environ.get('NFW_INVERT'):env['RUSTFLAGS']+=' --cfg NFW_invert'";s=s.replace(needle,needle+"\n if os.environ.get('NFW_BADARG'):env['RUSTFLAGS']+=' --cfg NFW_badarg'");p.write_text(s)
