include!("capacity-reference.rs");
fn main() {
    std::panic::set_hook(Box::new(|_|{}));
    let mut count=0;
    for n in 0..=1024 {
        let actual=String::with_capacity(n);
        let reference=deployed_capacity_reference(n);
        assert_eq!(actual,reference);
        assert_eq!(actual.len(),0);
        assert_eq!(actual.capacity(),n);
        assert_eq!(reference.capacity(),n);
        count+=1;
    }
    for n in [isize::MAX as usize+1,usize::MAX] {
        let actual=std::panic::catch_unwind(||String::with_capacity(n));
        let reference=std::panic::catch_unwind(||deployed_capacity_reference(n));
        assert!(actual.is_err() && reference.is_err());
        count+=1;
    }
    println!("PASS V181 {count} owned capacity Result/header pairs, including2 deterministic overflow panics; finite validation only");
}
