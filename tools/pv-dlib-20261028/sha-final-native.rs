use sha2::Sha256VarCore;
use digest::{Output,core_api::{Block,VariableOutputCore}};
use digest::block_buffer::{BlockBuffer,Eager};
use digest::typenum::U64;
#[path="padding-retained-reference.rs"] mod padding;

fn owned<F>(mut state:[u32;8],blocks:u64,bytes:[u8;64],pos:u8,mut compress:F)
    ->([u32;8],u64,[u8;64],u8,[u8;32])
where F:FnMut(&mut[u32;8],&[Block<Sha256VarCore>]) {
    let bits=8u64.wrapping_mul((pos as u64).wrapping_add(64u64.wrapping_mul(blocks)));
    let (events,count,retained)=padding::padding_retained_reference(bytes,pos as usize,bits);
    for b in events.iter().take(count) {
        compress(&mut state,core::slice::from_ref(&Block::<Sha256VarCore>::clone_from_slice(b)));
    }
    let out=core::array::from_fn(|i| (state[i/4]>>(8*(3-i%4))) as u8);
    (state,blocks,retained,0,out)
}

#[test] fn native_sha_finalize_differential() {
    let mut cases=0;
    for pos in 0..64u8 {for seed in [0u64,1,u64::MAX,0x123456789abcdef0] {
        let state=core::array::from_fn(|i|(seed.rotate_left((i*7) as u32) as u32).wrapping_add(i as u32));
        let bytes=core::array::from_fn(|i|(seed.rotate_left(i as u32) as u8).wrapping_add(i as u8));
        for blocks in [0,1,u64::MAX,seed] {
            let mut core=Sha256VarCore::pv_dl_from_state(state,blocks);
            let mut buffer=BlockBuffer::<U64,Eager>::pv_dl_from_snapshot(bytes,pos);
            let mut out:Output<Sha256VarCore>=Default::default();
            VariableOutputCore::finalize_variable_core(&mut core,&mut buffer,&mut out);
            let expected=owned(state,blocks,bytes,pos,Sha256VarCore::pv_dl_compress_slice);
            assert_eq!(core.pv_dl_state(),(expected.0,expected.1));
            assert_eq!(buffer.pv_dl_bytes(),expected.2.as_slice());assert_eq!(buffer.get_pos(),expected.3 as usize);
            assert_eq!(out.as_slice(),expected.4.as_slice());
            let mut core=Sha256VarCore::pv_dl_from_state(state,blocks);
            let mut buffer=BlockBuffer::<U64,Eager>::pv_dl_from_snapshot(bytes,pos);
            let mut out:Output<Sha256VarCore>=Default::default();
            core.pv_dl_finalize_param(&mut buffer,&mut out,Sha256VarCore::pv_dl_compress_slice);
            assert_eq!(core.pv_dl_state(),(expected.0,expected.1));
            assert_eq!(buffer.pv_dl_bytes(),expected.2.as_slice());assert_eq!(out.as_slice(),expected.4.as_slice());
            cases+=1;
        }
    }}
    println!("{cases} arbitrary-state native/parameterized/owned SHA finalizer cases; finite validation only");
}
