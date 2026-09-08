//! Exhaustive ALL-domain single-bit bridge, not a kernel certificate.
//! Avoid 1024 full codewords: each accessor follows only one butterfly path.
use super::*;
pub fn run(){
    let begin=std::time::Instant::now();
    let source=circle_candidate::CircleEncoder::new_for_domain_log(20);
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&(0..(1<<18)).collect::<Vec<_>>()).unwrap();
    let mut seen=std::collections::HashSet::with_capacity(1<<20);
    let mut checks=0;
    let i=CM31::new(M31::ZERO,M31::ONE);let two=CM31::from_m31(M31(2));
    let h=two.inv();let g=two.mul(i).inv();
    assert_eq!(i.square(),CM31::ONE.neg());assert_eq!(two.mul(h),CM31::ONE);assert_eq!(two.mul(i).mul(g),CM31::ONE);
    for(fibre,p)in pts.iter().enumerate(){
        let slots=[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)];
        for(slot,(x,y))in slots.into_iter().enumerate(){
            assert!(seen.insert((x.0,y.0)),"duplicate realized circle point");
            assert_eq!(x.mul(x).add(y.mul(y)),M31::ONE);
            let z=CM31::new(x,y);assert_ne!(z,CM31::ZERO);
            assert_eq!(h.mul(z.square().add(CM31::ONE)),z.mul_m31(x));
            assert_eq!(g.mul(z.square().sub(CM31::ONE)),z.mul_m31(y));
            let mut v=x;
            for bit in 0..10{let expected=if bit==0{y}else{let value=v;v=v.mul(v).double().sub(M31::ONE);value};
                assert_eq!(source.encode_c1_basis_value(1<<bit,4*fibre+slot).unwrap(),expected,
                    "source coordinate at fibre {fibre} slot {slot} bit {bit}");checks+=1;}
        }
    }
    println!("ALL_DOMAIN_COORDINATES domain_log=20 distinct_points={} single_bit_source_checks={checks} circle_and_CM31_scaling=true seconds={}",seen.len(),begin.elapsed().as_secs_f64());
}
