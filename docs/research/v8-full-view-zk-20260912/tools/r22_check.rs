mod r22_native;
use aspis_core::field::{QM31 as K,CM31,M31,P};
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),4);
    let out=std::path::Path::new(&args[1]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let mut seed=0x9122_ffee_abcd_1234u64;
    let mut sample=||{let mut limb=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;M31(seed as u32%P)};K{c0:CM31::new(limb(),limb()),c1:CM31::new(limb(),limb())}};
    for case in 0..256 {
        let x:[K;24]=core::array::from_fn(|_|match case{0=>K::ZERO,1=>K::ONE,2=>{let p=M31(P-1);K{c0:CM31::new(p,p),c1:CM31::new(p,p)}},_=>sample()});
        assert_eq!(r22_native::compute(&x),r22_native::compute_scalar(&x),"source case {case}");
        if case<4 {r22_native::check_adjoint(&x);}
    }
    for world in 0..2 {
        let b=std::fs::read(&args[2+world]).unwrap();assert_eq!(b.len(),384);
        let x:[K;24]=core::array::from_fn(|i|K::from_le_bytes(&b[16*i..16*i+16]).unwrap());
        let expected=r22_native::compute(&x);assert_eq!(expected,r22_native::compute_scalar(&x));
        let mut wire=b;wire.extend_from_slice(&[0u8;16]);expected.write_le_bytes(&mut wire[384..400]);
        std::fs::write(out.join(format!("world{world}.bin")),wire).unwrap();
    }
    println!("R22_NATIVE source_vectors=256 adjoint_basis_cases=4096 genuine_public_inputs=2 image_retained=true T_unchanged=true auxiliary_proof=false");
}
