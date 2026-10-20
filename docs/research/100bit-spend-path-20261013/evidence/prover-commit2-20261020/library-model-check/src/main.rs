use std::ops::Deref;
use zeroize::Zeroizing;
fn check(value: [u8;32]) {
    let wrapped=Zeroizing::new(value);
    let slice: &[u8]=wrapped.as_ref();
    assert_eq!(slice.len(),32);
    assert_eq!(slice,&value);
    assert_eq!(*wrapped.deref(),value);
    for (i,&byte) in slice.iter().enumerate() {assert_eq!(byte,value[i]);}
}
fn main() {
    assert!(!cfg!(debug_assertions));
    assert_eq!(aspis_core::field::P,2147483647);
    assert_eq!(aspis_core::r0::FIBRE_COUNT,262144);
    let mut cases=0usize;
    for byte in 0..=255 {check([byte;32]);cases+=1;}
    let mut state=0x9e3779b97f4a7c15u64;
    for _ in 0..65536 {
        let mut bytes=[0u8;32];
        for byte in &mut bytes {
            state=state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            *byte=(state>>32) as u8;
        }
        check(bytes);cases+=1;
    }
    let mut calls=0;
    let ok: Result<u32,u32>=Ok(17);
    assert_eq!(ok.map(|x|{calls+=1;x+5}),Ok(22));
    let err: Result<u32,u32>=Err(19);
    assert_eq!(err.map(|x|{calls+=1;x+5}),Err(19));
    assert_eq!(calls,1);
    println!("{{\"live_payload_cases\":{cases},\"result_map_cases\":2,\"constants_checked\":2,\"passed\":true}}");
}
