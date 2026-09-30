extern crate aspis_core as corelib;
use corelib::field::{M31,CM31,QM31 as K};
const Q:usize=22;
#[derive(Debug,PartialEq)] enum Error{Shape,Domain}
mod circle_norm;
mod quotient_fold;
// Predecessor helpers remain compiled for the retained module, not selected.
fn batch_inverse_m(v:&[M31])->Result<Vec<M31>,Error>{v.iter().map(|x|if *x==M31::ZERO{Err(Error::Domain)}else{Ok(x.inv())}).collect()}
fn main(){
    let mut rng=0x99cafe1234567890u64;
    fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P))as u32)}
    fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
    let mut weights_checked=0;let mut folds=0;let mut domain=0;
    for case in 0..4096 {
        let n=1+case%22;let ids:Vec<_>=(0..n).map(|j|((case*137+j*11971)%262144)as u32).collect();
        let selected=circle_norm::Selected::new(&ids).unwrap();let pts=selected.points();
        let mut abc=core::array::from_fn(|_|k(&mut rng));
        if case<3 {abc=[[K::ONE,K::ZERO,K::ZERO],[K::ZERO,K::ONE,K::ZERO],[K::ZERO,K::ZERO,K::ONE]][case];}
        if case%31==0 {abc=[K::ZERO;3];}
        if case%23==0 {abc[0]=abc[1].mul_m31(pts[0].x).add(abc[2].mul_m31(pts[0].y)).neg();}
        let values:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)]
            .map(|(x,y)|abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))).collect();
        let base:Vec<_>=pts.iter().flat_map(|p|[p.x.double(),p.y.double()]).collect();
        let lines:Vec<_>=pts.iter().map(|p|p.x.mul(p.x).double().sub(M31::ONE)).collect();
        let alpha=if case%17==0{K::ZERO}else if case%19==0{K::ONE}else{k(&mut rng)};
        let got=selected.inverse_folded(&values,abc,&base,&lines,alpha);
        let old=selected.inverse_lines(&values,abc,&base,&lines);
        if values.contains(&K::ZERO) {assert_eq!(got,Err(Error::Domain));assert_eq!(old,Err(Error::Domain));domain+=1;continue;}
        let weights=got.unwrap();let (inverse,base_inverse)=old.unwrap();
        for (i,p) in pts.iter().enumerate(){
            let ix=base_inverse[2*i];let iy=base_inverse[2*i+1];
            for slot in 0..4 {
                let basis=core::array::from_fn(|j|if j==slot{K::ONE}else{K::ZERO});
                let w=corelib::field::qm31_circle_to_line_fold4(basis,alpha,ix,iy);
                assert_eq!(weights[4*i+slot],w.mul(inverse[4*i+slot]));
                // Direct inversions are independent of the shared norm path.
                assert_eq!(values[4*i+slot].mul(inverse[4*i+slot]),K::ONE);
                weights_checked+=1;
            }
            let iv=[k(&mut rng),k(&mut rng)];let all=core::array::from_fn(|_|k(&mut rng));
            let weighted=quotient_fold::Weighted::new(iv).unwrap();
            for use_x in [false,true] {
                let h=if use_x{p.x}else{p.y};let delta=iv[1].mul_m31(h);
                let q=core::array::from_fn(|j|all[j].sub(iv[0].add(if if use_x{j<2}else{j==0||j==3}{delta}else{delta.neg()})).mul(inverse[4*i+j]));
                assert_eq!(weighted.fold(all,weights[4*i..4*i+4].try_into().unwrap(),h,use_x),
                    Some(corelib::field::qm31_circle_to_line_fold4(q,alpha,ix,iy)));folds+=1;
            }
        }
    }
    let selected=circle_norm::Selected::new(&[0]).unwrap();
    assert_eq!(selected.inverse_folded(&[],[K::ZERO;3],&[],&[],K::ONE),Err(Error::Shape));
    assert_eq!(selected.inverse_folded(&[K::ONE;4],[K::ONE,K::ZERO,K::ZERO],&[M31::ZERO,M31::ONE],&[M31::ONE],K::ONE),Err(Error::Domain));
    let empty=circle_norm::Selected::new(&[]).unwrap();
    assert_eq!(empty.inverse_folded(&[],[K::ZERO;3],&[],&[],K::ONE),Err(Error::Domain));
    let w=quotient_fold::Weighted::new([K::ONE;2]).unwrap();let mut malformed=0;
    for limb in 0..4 {for raw in [corelib::field::P,corelib::field::P+1,u32::MAX] {
        let mut b=[M31::ZERO;4];b[limb]=M31(raw);let v=K{c0:CM31::new(b[0],b[1]),c1:CM31::new(b[2],b[3])};
        assert!(quotient_fold::Weighted::new([v,K::ZERO]).is_none());
        assert!(quotient_fold::Weighted::new([K::ZERO,v]).is_none());
        for slot in 0..4 {let mut all=[K::ZERO;4];all[slot]=v;
            assert!(w.fold(all,[K::ZERO;4],M31::ONE,true).is_none());
            assert!(w.fold([K::ZERO;4],all,M31::ONE,false).is_none());malformed+=2;}
        assert!(w.fold([K::ZERO;4],[K::ZERO;4],M31(raw),false).is_none());malformed+=3;
    }}
    println!("R99_FOLD profiles=4096 weights={weights_checked} complete_folds={folds} zero_chords={domain} malformed={malformed} alpha_zero_one=true checks_retained=true");
}
