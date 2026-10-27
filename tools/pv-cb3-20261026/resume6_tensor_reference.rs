//! cfg(kani) P6 tensor component: fixed owned destructuring, no indexed loans.
//! Native association is not inherited from earlier references.
use aspis_core::field::QM31 as K;
pub fn pick4(xs:[K;4],i:usize)->K {
    let [a,b,c,d]=xs;
    match i {0=>a,1=>b,2=>c,3=>d,_=>panic!("tensor digit out of range")}
}
pub fn plane(xs:[[K;4];5],j:usize)->K {
    let [a,b,c,d,e]=xs;
    let a=pick4(a,j&3);
    let b=pick4(b,(j>>2)&3);
    let c=pick4(c,(j>>4)&3);
    let d=pick4(d,(j>>6)&3);
    let e=pick4(e,(j>>8)&3);
    K::ONE.mul(a).mul(b).mul(c).mul(d).mul(e)
}
pub fn tensor(xs:[[[K;4];5];5],k:usize,j:usize)->K {
    let [a,b,c,d,e]=xs;
    match k {0=>plane(a,j),1=>plane(b,j),2=>plane(c,j),3=>plane(d,j),4=>plane(e,j),
        _=>panic!("tensor plane out of range")}
}
