from pathlib import Path
import hashlib,json
root=Path.cwd();e=root/'evidence/pv-l2b-20261027'
p=root/'crates/aspis-prover/src/state_only_entropy.rs';s=p.read_text();start=s.index('fn entropy_nonzero32(');end=s.index('\n}',start)+2;function=s[start:end]
header='''use std::convert::TryInto;
// Literal source predicate plus six control/indexing gates. No field chains or stubs.
'''+function+'\n'
body='''
#[kani::proof]
fn mask_range() {
 let raw:u32=kani::any();let candidate=raw & 0x7fff_ffff;
 assert!(candidate<=2147483647);
}
#[kani::proof]
fn reject_exactly_last() {
 let raw:u32=kani::any();let candidate=raw & 0x7fff_ffff;
 assert!((candidate<2147483647)==(candidate!=2147483647));
}
#[kani::proof]
fn high_bit_fibres() {
 let low:u32=kani::any();kani::assume(low<=2147483647);
 let high:bool=kani::any();let raw=low | ((high as u32)<<31);
 assert!((raw & 0x7fff_ffff)==low);
 assert!(((raw>>31)!=0)==high);
}
#[kani::proof]
#[kani::unwind(33)]
fn entropy_zero_iff() {
 let bytes:[u8;32]=kani::any();
 assert!(entropy_nonzero32(&bytes)==(bytes!=[0;32]));
}
#[kani::proof]
#[kani::unwind(33)]
fn entropy_marker() {
 let index:usize=kani::any();kani::assume(index<32);
 let v:u8=kani::any();kani::assume(v!=0);
 let mut bytes=[0u8;32];bytes[index]=v;
 assert!(entropy_nonzero32(&bytes));
}
#[kani::proof]
fn cursor_slice() {
 let word:usize=kani::any();kani::assume(word<8);
 let block:[u8;32]=kani::any();
 let start=4*word;
 let value=u32::from_le_bytes(block[start..start+4].try_into().unwrap());
 assert!(start+3<32);assert!(word+1<=8);
 assert!(value==u32::from_le_bytes([block[start],block[start+1],block[start+2],block[start+3]]));
}
'''
(e/'control.rs').write_text(header+body)
(e/'control-source.json').write_text(json.dumps({'revision':'c57a344726745387efb38d1571d885c69ce829ee','source':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'literal_predicate_sha256':hashlib.sha256(function.encode()).hexdigest(),'scope':'No-stub standalone exact entropy predicate; mask and cursor expression projections only, not a shipped-function equivalence gate.'},indent=2)+'\n')
