include!("selected.rs");
// This process alone receives the filter. The selected function and its real
// getrandom dependency are unchanged; the kernel supplies an ordinary error.
fn main() {
    let mut filter = [
        libc::sock_filter {code:0x20,jt:0,jf:0,k:0}, // load seccomp_data.nr
        libc::sock_filter {code:0x15,jt:0,jf:1,k:libc::SYS_getrandom as u32},
        libc::sock_filter {code:0x06,jt:0,jf:0,k:0x00050000 | libc::EPERM as u32},
        libc::sock_filter {code:0x06,jt:0,jf:0,k:0x7fff0000},
    ];
    let program=libc::sock_fprog {len:filter.len() as u16,filter:filter.as_mut_ptr()};
    assert_eq!(unsafe {libc::prctl(libc::PR_SET_NO_NEW_PRIVS,1,0,0,0)},0);
    assert_eq!(unsafe {libc::prctl(libc::PR_SET_SECCOMP,libc::SECCOMP_MODE_FILTER,&program)},0);
    match StateOnlyAttemptSecrets::generate_for_mask_nonce([1;32]) {
        Err(StateOnlyAttemptEntropyError::Os(error)) => {
            assert_eq!(error.raw_os_error(),Some(libc::EPERM));
            println!("unchanged factory: nonzero nonce -> Os(EPERM); no proof body entered");
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock) => panic!("wrong error"),
        Ok(_) => panic!("kernel getrandom refusal must not yield secrets"),
    }
}
