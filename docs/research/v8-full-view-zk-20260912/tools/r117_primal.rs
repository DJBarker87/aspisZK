#[path="r81_canonical_basis.rs"]mod r117_private;
use r117_private::Q as CQ;
fn r117_in(v:K)->Option<CQ>{CQ::from_limbs([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0])}
fn r117_out(v:CQ)->K{let v=v.limbs().map(super::M31);K{c0:super::corelib::field::CM31::new(v[0],v[1]),c1:super::corelib::field::CM31::new(v[2],v[3])}}
#[inline(always)]
fn r117_block(v:&[K],powers:&[CQ;3])->Option<K>{
    Some(r117_out(CQ::affine3(r117_in(v[0])?,powers,[r117_in(v[1])?,r117_in(v[2])?,r117_in(v[3])?])))
}
#[cold]#[inline(never)]
fn r117_raw_block(v:&[K],a:K)->K{
    let a2=a.square();let ps=[P::new(a),P::new(a2),P::new(a2.mul(a))];
    qm31_add_sum_products3_prepared(v[0],&ps,&[v[1],v[2],v[3]])
}
pub(super) fn fold(mut v:Vec<K>,a:K)->Vec<K>{
    let Some(ca)=r117_in(a)else{return r117_retained_fold(v,a)};
    let a2=ca.square();let powers=[ca,a2,a2.mul(ca)];let n=v.len()/4;
    for i in 0..n{
        let block=&v[4*i..4*i+4];
        let value=r117_block(block,&powers).unwrap_or_else(||r117_raw_block(block,a));
        v[i]=value;
    }
    v.truncate(n);v
}
#[cfg(not(target_os="solana"))]
pub(super) fn controls(){
    use super::corelib::field::{M31,CM31,P};
    let mut state=0x117cccc53216u64;
    fn k(s:&mut u64)->K{let mut m=||{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;M31((*s%u64::from(P))as u32)};K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())}}
    let mut coordinates=0;let mut tail=0;
    for case in 0..4096{
        let n=[0,1,3,4,5,16,64,256][case%8];
        let mut values:Vec<_>=(0..n).map(|_|k(&mut state)).collect();
        let a=match case%19{0=>K::ZERO,1=>K::ONE,2=>{let m=M31(P-1);let v=K{c0:CM31::new(m,m),c1:CM31::new(m,m)};values.fill(v);v},_=>k(&mut state)};
        let got=fold(values.clone(),a);let old=r117_retained_fold(values.clone(),a);assert_eq!(got,old);coordinates+=got.len();
        let independent:Vec<_>=values.chunks_exact(4).map(|v|v[0].add(a.mul(v[1].add(a.mul(v[2].add(a.mul(v[3]))))))).collect();
        assert_eq!(got,independent);
        if n==256{let mut got=values.clone();let mut old=values;for _ in 0..3{let a=k(&mut state);got=fold(got,a);old=r117_retained_fold(old,a);assert_eq!(got,old);tail+=1;}}
    }
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));let mut raw=0;
    for limb in 0..4{for bad in [P,P+1,u32::MAX]{
        let mut v=[M31::ZERO;4];v[limb]=M31(bad);let bad=K{c0:CM31::new(v[0],v[1]),c1:CM31::new(v[2],v[3])};
        for pos in 0..18{
            let mut values=vec![K::ONE;17];let a=if pos==17{bad}else{values[pos]=bad;K::ONE};
            let got=std::panic::catch_unwind(||fold(values.clone(),a));
            let old=std::panic::catch_unwind(||r117_retained_fold(values,a));
            assert_eq!(got.is_ok(),old.is_ok());if let(Ok(g),Ok(o))=(got,old){assert_eq!(g,o);}raw+=1;
        }
    }}
    std::panic::set_hook(hook);
    println!("R117_PRIMAL profiles=4096 folded_coordinates={coordinates} tail_stage_checks={tail} raw_boundary_cases={raw} trailing_partial_preserved=true independent_horner=true");
}
