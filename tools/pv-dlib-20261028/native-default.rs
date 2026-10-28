#[path="default-reference.rs"] mod reference;
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(70)]
fn sha256_default_snapshot() {
    let native:sha2::Sha256=Default::default();
    let (core,buffer)=native.decompose();
    let (state,blocks)=core.pv_dl_inner().pv_dl_snapshot();
    let (rs,rb,rbuf,rp)=reference::default_reference();
    assert_eq!(state,rs);
    assert_eq!(blocks,rb);
    assert_eq!(buffer.get_pos(),rp);
    assert_eq!(buffer.pv_dl_bytes(),&rbuf);
}

pub fn native_default() -> sha2::Sha256 { Default::default() }

#[cfg(kani)] mod generic_default_gate {
    use digest::core_api::{BlockSizeUser,BufferKindUser,CoreWrapper};
    use digest::typenum::U64;
    #[derive(Clone,Copy,Debug,Eq,PartialEq)] struct Core([u32;8]);
    // A deterministic, explicitly seeded trait input; no function is stubbed.
    static mut DEFAULT_STATE:[u32;8]=[0;8];
    impl Default for Core {fn default()->Self {Self(unsafe {DEFAULT_STATE})}}
    impl BlockSizeUser for Core {type BlockSize=U64;}
    impl BufferKindUser for Core {type BufferKind=digest::block_buffer::Eager;}
    #[kani::proof]
    #[kani::unwind(70)]
    fn wrapper_default_arbitrary_core() {
        let state:[u32;8]=kani::any();
        unsafe {DEFAULT_STATE=state;}
        let native:CoreWrapper<Core>=Default::default();
        let (core,buffer)=native.decompose();
        let (rc,rb,rp)=super::reference::wrap_reference(Core(state));
        assert_eq!(core,rc);
        assert_eq!(buffer.pv_dl_bytes(),&rb);
        assert_eq!(buffer.get_pos(),rp);
    }
}

#[cfg(kani)] #[path="update-gate.rs"] mod update_gate;
#[cfg(kani)] #[path="padding-gate.rs"] mod padding_gate;
