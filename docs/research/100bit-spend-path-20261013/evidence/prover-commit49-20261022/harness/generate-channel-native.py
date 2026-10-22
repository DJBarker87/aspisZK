from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'channel-binding.rs' not in s:s+='\ninclude!("channel-binding.rs");\n'
p.write_text(s)
(E/'native/channel-binding.rs').write_text('''
fn native_channel49(mut sums:[[u64;3];3],a:[[u32;3];3],b:[[u32;3];3],c:usize,h:usize,product:u64)->([[u64;3];3],(u32,u32)) {
 let operands=(a[c][h],b[c][h]);sums[c][h]+=product;(sums,operands)
}
fn owner_channel49(mut sums:[[u64;3];3],a:[[u32;3];3],b:[[u32;3];3],c:usize,h:usize,product:u64)->([[u64;3];3],(u32,u32)) {
 let operands=(a[c][h],b[c][h]);sums[c][h]=sums[c][h].wrapping_add(product);(sums,operands)
}
#[cfg(kani)] mod channel_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(12)] fn integer_channel_iteration() {
  let sums:[[u64;3];3]=kani::any();let a:[[u32;3];3]=kani::any();let b:[[u32;3];3]=kani::any();
  let c:usize=kani::any();let h:usize=kani::any();kani::assume(c<3 && h<3);
  let product:u64=kani::any();kani::assume(product<=2147483646u64*2147483646u64);
  kani::assume(sums[c][h]<=2*2147483646u64*2147483646u64);
  let x=native_channel49(sums,a,b,c,h,product);let y=owner_channel49(sums,a,b,c,h,product);
  for r in 0..3 {for s in 0..3 {assert_eq!(x.0[r][s],y.0[r][s]);}}assert_eq!(x.1,y.1);
 }
}
''')

p=Path('crates/aspis-core/src/field.rs')
(E/'pins/channel-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=[524,529],binding='Nine-channel update after the verified integer-product callee. Universal product <= (P-1)^2 and two-product prior total; exact selected operand pair and whole surrounding matrix. NativeSquare49.mul64 and ChannelSum49.product_bound independently justify the abstract callee and bound. v1 with inline multiplication timed out at 180s; v2 changes the proof scope, not caps. Component construction and reconstruction remain pending.'),indent=2)+'\n')
