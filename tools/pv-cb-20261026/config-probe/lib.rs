#[cfg(kani)]
#[kani::proof]
fn config_probe() {
    let x: u8 = kani::any();
    assert_eq!(x.wrapping_add(0), x);
}
