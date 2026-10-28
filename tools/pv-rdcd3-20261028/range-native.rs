// Focused finite library validation, not unbounded Rust or binary refinement.
fn reference(mut start: usize, stop: usize, mut acc: u64) -> u64 {
    while start < stop {
        let old = start;
        start += 1;
        acc = mix(acc, old);
    }
    acc
}
fn mix(acc: u64, index: usize) -> u64 {
    (acc.rotate_left(11) ^ index as u64).wrapping_mul(0x9e3779b97f4a7c15)
}
fn check(start: usize, stop: usize) -> usize {
    let mut actual = start..stop;
    let mut cursor = start;
    let mut count = 0;
    loop {
        let expected = if cursor < stop {let old=cursor;cursor+=1;Some(old)} else {None};
        assert_eq!(actual.next(),expected);
        assert_eq!(actual.start,cursor);
        assert_eq!(actual.end,stop);
        count+=1;
        if expected.is_none() {break;}
    }
    assert_eq!((start..stop).fold(7u64,mix),reference(start,stop,7));
    count
}
fn main() {
    assert_eq!(usize::BITS,64);
    let mut cases=0;let mut transitions=0;
    for start in 0usize..65 {for stop in 0usize..65 {
        transitions+=check(start,stop);cases+=1;
    }}
    for delta in 0usize..65 {for len in 0usize..=delta {
        transitions+=check(usize::MAX-delta,usize::MAX-delta+len);cases+=1;
    }}
    transitions+=check(usize::MAX,0);cases+=1;
    println!("range cases={cases}; next transitions={transitions}; ordered folds={cases}; finite validation only");
}
