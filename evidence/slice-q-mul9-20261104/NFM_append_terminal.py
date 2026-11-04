from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFM_FRAME_PAYLOAD.json').read_text());k='crates/aspis-r1-cost-probe/src/NFM_dots.rs';s=p[k]
s+='''
// Typed native certificate for the conservative inventory's value.add
// alternatives. The frozen final receiver is WideExact, not M31/CM31/QM31.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFM_copy::KMX_copy_nonoverlapping)]
fn terminal_selected_add(){
 let head:WideExact=kani::any();let tail:WideExact=kani::any();
 let a=head.to_limbs();let b=tail.to_limbs();
 for i in 0..8{kani::assume(a[i]<2147483647 && b[i]<2147483647);}
 let lane:usize=kani::any();kani::assume(lane<8);
 let value:WideExact=head.add(tail);
 let sum=a[lane]+b[lane];let expected=if sum>=2147483647{sum-2147483647}else{sum};
 assert_eq!(value.to_limbs()[lane],if cfg!(NFM_wrong_terminal_add){expected^1}else{expected});
}
'''
p[k]=s;(E/'NFM_STRICT_PAYLOAD.json').write_text(json.dumps(p))
