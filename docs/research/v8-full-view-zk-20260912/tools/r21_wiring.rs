//! Fixed, reduced wiring polynomial. No prover-supplied program or map.
use super::{Circuit, K, bits, equality_table};
#[path="r21_wiring_tables.rs"] mod tables;
pub use tables::MAX_NODES;

#[inline(never)]
pub fn endpoint(level:usize,z:&[K],u:&[K],v:&[K],a:K,b:K,work:&mut[K])->K {
    let layer=&tables::LAYERS[level];
    assert_eq!(z.len(),layer.z);assert_eq!(u.len(),layer.k);assert_eq!(v.len(),layer.k);
    assert!(work.len()>=layer.nodes.len()+5);
    let mut x=[K::ZERO;27];let mut complement=[K::ZERO;27];
    let n=z.len()+u.len()+v.len();
    for(i,&r)in z.iter().chain(u).chain(v).enumerate(){x[i]=r;complement[i]=K::ONE.sub(r);}
    work[0]=K::ZERO;work[1]=a.add(b);work[2]=a.mul(b);work[3]=a.sub(b);work[4]=a;
    for(i,&(variable,low,high))in layer.nodes.iter().enumerate(){
        let j=variable as usize;assert!(j<n);
        let l=work[low as usize];let h=work[high as usize];
        work[5+i]=if low==0{x[j].mul(h)}else if high==0{complement[j].mul(l)}else{l.add(x[j].mul(h.sub(l)))};
    }
    work[layer.root]
}

#[cfg(not(target_os="solana"))]
pub fn check(c:&Circuit){
    use aspis_core::field::{CM31,M31,P};
    assert_eq!(c.layers.len(),tables::LAYERS.len());
    let mut seed=0x1122_3321_9468_9876u64;
    let mut random=||{let mut next=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;M31(seed as u32%P)};K{c0:CM31::new(next(),next()),c1:CM31::new(next(),next())}};
    let mut checks=0;let mut work=vec![K::ZERO;MAX_NODES];
    for case in 0..32 {
        for (level,layer) in c.layers.iter().enumerate(){
            let previous=if level==0{c.inputs.len()}else{c.layers[level-1].len()};
            let mut value=||if case==0{K::ZERO}else if case==1{K::ONE}else{random()};
            let z:Vec<_>=(0..bits(layer.len())).map(|_|value()).collect();
            let u:Vec<_>=(0..bits(previous)).map(|_|value()).collect();
            let v:Vec<_>=(0..bits(previous)).map(|_|value()).collect();
            let a=value();let b=value();
            let mut ez=vec![K::ZERO;1<<z.len()];let mut eu=vec![K::ZERO;1<<u.len()];let mut ev=vec![K::ZERO;1<<v.len()];
            equality_table(&z,&mut ez);equality_table(&u,&mut eu);equality_table(&v,&mut ev);
            let terms=[a.add(b),a.mul(b),a.sub(b),a,K::ZERO];
            let direct=layer.iter().enumerate().fold(K::ZERO,|s,(g,gate)|s.add(ez[g].mul(eu[gate.1 as usize]).mul(ev[gate.2 as usize]).mul(terms[gate.0 as usize])));
            assert_eq!(endpoint(level,&z,&u,&v,a,b,&mut work),direct,"wiring layer {level} case {case}");checks+=1;
        }
    }
    println!("R21_STRUCTURED_WIRING checks={checks} arbitrary_full_QM31=true");
}
