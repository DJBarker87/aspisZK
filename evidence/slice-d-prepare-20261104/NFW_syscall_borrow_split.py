from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent;C='programs/r1-cost-probe/src/';p=E/'NFW_syscall.rs.txt';old=p.read_text()
copy=old[old.index('#[kani::proof]',old.index('fn syscall_bytes')):]
s='''use solana_program::hash::Hash;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log<'a>{reply:[u8;32],calls:usize,parts:Option<&'a[&'a[u8]]>}
// Exact frozen expression. The call cut records the ACTUAL typed immutable
// borrow, whose lifetime is the input lifetime. No buffer is read or written;
// no reference or guard is fabricated from integers or bytes.
fn syscall_cut<'a>(parts:&'a[&'a[u8]],log:&mut Log<'a>)->[u8;32]{
 let mut hashv=|xs:&'a[&'a[u8]]|{log.calls+=1;log.parts=Some(if cfg!(NFW_badarg){&xs[1..]}else{xs});Hash::new_from_array(log.reply)};
 hashv(parts).to_bytes()
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn syscall_bytes(){
 let data:[[u8;57607];5]=kani::any();let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(lengths[i]<=57607);i+=1;}
 let count:usize=kani::any();kani::assume(count>=1&&count<=5);
 let parts:[&[u8];5]=[&data[0][..lengths[0]],&data[1][..lengths[1]],&data[2][..lengths[2]],&data[3][..lengths[3]],&data[4][..lengths[4]]];
 let input=&parts[..count];let mut log=Log{reply:kani::any(),calls:0,parts:None};
 let result=syscall_cut(input,&mut log);let word:usize=kani::any();kani::assume(word<32);
 assert_eq!(log.calls,1);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 assert!(core::ptr::eq(log.parts.unwrap(),input));
}
'''+copy
p.write_text(s);x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x[C+'NFW_syscall.rs']=s;(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x[C+'NFW_syscall.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NFW_syscall_borrow_split.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/NFW_syscall.rs',tofile='b/NFW_syscall.rs')))
(E/'NFW_K020_REVIEW.json').write_text(json.dumps(dict(attempt='NFW_K020',disposition='TIMEOUT; zero credit',wall_seconds=117.52783031901345,peak_rss_kib=6351344,swaps=0,replacement='Typed immutable borrowed-argument recording with no payload reads. A source write-footprint and Lean frame proof are still required before byte-identity credit. No cap/time increase.'),indent=1)+'\n')
