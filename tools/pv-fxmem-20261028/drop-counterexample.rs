use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
static PANIC: AtomicBool = AtomicBool::new(false);
static DROPS: AtomicUsize = AtomicUsize::new(0);
// One inhabited zero-sized native input type. The input itself has no flag.
struct Input;
impl Drop for Input {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
        if PANIC.load(Ordering::SeqCst) { panic!("external destructor flag"); }
    }
}
fn reference(x: Input) { drop(x); }
fn run(flag: bool, owned_reference: bool) -> (bool, usize) {
    PANIC.store(flag, Ordering::SeqCst);
    DROPS.store(0, Ordering::SeqCst);
    let result = std::panic::catch_unwind(|| {
        if owned_reference { reference(Input) } else { core::mem::drop(Input) }
    });
    (result.is_ok(), DROPS.load(Ordering::SeqCst))
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    assert_eq!(std::mem::size_of::<Input>(), 0);
    let mut checks = 0;
    for _ in 0..16 {
        for flag in [false, true] {
            let native = run(flag, false);
            let reference = run(flag, true);
            assert_eq!(native, reference);
            assert_eq!(native, (!flag, 1));
            checks += 1;
        }
    }
    println!("FINITE VALIDATION: {checks} paired same-input cases; ZST Input; false => return, true => panic; exactly one destructor entry in each case");
    println!("COUNTEREXAMPLE: identical native input Input, worlds differing only in an external AtomicBool, unequal complete Result classifications");
    println!("Boundary: unwind test policy; no binary erasure, allocator trace or deployed-path claim");
}
