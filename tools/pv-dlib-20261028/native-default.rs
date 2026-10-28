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
