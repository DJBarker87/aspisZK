//! Exact regrouping; source creates every event and applies domain tweaks.
use crate::{canonical::{Q,P},whole_dot::Dot};
pub fn basis(x:Q,out:&mut[Q;27]){
    out[0]=Q::ONE.sub(x.add(x));let mut power=x.mul(x);
    for i in 1..27{out[i]=power.sub(x);if i!=26{power=power.mul(x)}}
}
pub fn step(claim:Q,sent:&[Q;27],x:Q,cache:&mut[Q;27])->Q{
    basis(x,cache);let mut d=Dot::new();for i in 0..27{d.push(sent[i],cache[i]).unwrap()}claim.mul(x).add(d.finish())
}
fn pack(v:[Q;4])->Q{
    // Source adapter must check correspondence with qm31_pack_base4.
    let basis=[Q::ONE,Q::from_limbs([0,1,0,0]).unwrap(),Q::from_limbs([0,0,1,0]).unwrap(),Q::from_limbs([0,0,0,1]).unwrap()];
    let mut d=Dot::new();for i in 0..4{d.push(v[i],basis[i]).unwrap()}d.finish()
}
pub struct Event {pub group:usize,pub high:Q,pub expected:[u32;8]}
/// Groups correspond to locals 0,11,12. Source must preserve optional events,
/// all levels, the carry case and tweak-canonicalization before calling here.
pub fn digest_constraints(opened:&[Q;16],events:&[Event])->Option<[[Q;2];3]>{
    if events.len()>4096{return None}
    let mut sums=[Q::ZERO;3];let mut expected=[[Dot::new();2];3];
    for e in events{if e.group>=3||e.expected.iter().any(|&x|x>=P){return None}
        sums[e.group]=sums[e.group].add(e.high);
        for h in 0..2{expected[e.group][h].push(e.high,Q::from_limbs(e.expected[4*h..4*h+4].try_into().ok()?)?).ok()?}
    }
    Some(core::array::from_fn(|g|core::array::from_fn(|h|{
        let start=if g==0 {8+4*h}else{4*h};
        sums[g].mul(pack(opened[start..start+4].try_into().unwrap())).sub(expected[g][h].finish())
    })))
}
