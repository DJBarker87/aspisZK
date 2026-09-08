// Exact tiny-field falsification/regression, run with rustc -O. No sampling.
fn value(p: u32, e: [u32; 4], k: u32) -> u32 {
    e.iter().rev().fold(0, |a, c| (a * k + c) % p)
}
fn main() {
    let mut tuples = 0;
    let mut sharp = 0;
    for p in [3, 5, 7, 11] {
        for i in 0..p { for e0 in 0..p { for e1 in 0..p { for e2 in 0..p {
            let e = [i, e0, e1, e2];
            if e == [0; 4] { continue; }
            let roots = (1..p).filter(|&k| value(p, e, k) == 0).count();
            assert!(roots <= 3);
            if roots == 3 { sharp += 1; }
            tuples += 1;
        }}}}
        for delta in 1..p { for k in 1..p {
            assert_eq!((p-delta+delta+k*0+k*k*0)%p, 0);
            assert_eq!(value(p, [p-delta,delta,0,0], k)==0, k==1);
            // Timing regression: choosing the inactive claim after kappa
            // defeats the repaired batch too. This must be forbidden.
            let late_inactive = (p - k*delta%p)%p;
            assert_eq!(value(p, [late_inactive,delta,0,0], k), 0);
        }}
        if p > 3 {
            // (X-1)(X-2)(X-3): the numerator three is genuinely needed.
            let e = [(p-6%p)%p, 11%p, (p-6%p)%p, 1];
            assert_eq!((1..p).filter(|&k| value(p,e,k)==0).count(), 3);
        }
    }
    println!("PASS {tuples} nonzero coefficient tuples; {sharp} three-root cases; constant-cancellation, kappa=1 and late-inactive regressions");
}
