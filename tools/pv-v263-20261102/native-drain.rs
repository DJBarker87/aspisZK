extern crate alloc;
#[path = "../../evidence/pv-v263-20261102/inputs/crates/aspis-r1-cost-probe/src/host_work.rs"]
mod host_work;
#[path = "../../evidence/pv-v263-20261102/inputs/docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
mod pool;
fn main() {
    let counts = [0, 2, 27, 28, 56, 112, 224, 448, 896, 1792, 3584, 7168, 14336];
    let mut checks = 0;
    for n in counts {
        let mut output = Vec::<Result<u64,u64>>::with_capacity(n);
        let initial_capacity = output.capacity();
        for k in 0..16 {
            let (a,b) = pool::range(n,k);
            let mut chunk = Vec::with_capacity(b-a);
            for i in a..b { chunk.push(if i%7==0 {Err(i as u64)} else {Ok(i as u64)}); }
            let donor_capacity = chunk.capacity();
            let donor_pointer = chunk.as_ptr();
            let output_pointer = output.as_ptr();
            let before = output.len();
            output.append(&mut chunk);
            assert_eq!(output.len(), before+b-a);
            assert!(chunk.is_empty());
            assert_eq!(chunk.capacity(), donor_capacity);
            assert_eq!(chunk.as_ptr(), donor_pointer);
            assert_eq!(output.capacity(), initial_capacity);
            assert_eq!(output.as_ptr(), output_pointer);
            checks+=1;
        }
        assert_eq!(output, (0..n).map(|i|if i%7==0 {Err(i as u64)} else {Ok(i as u64)}).collect::<Vec<_>>());
        let actual = host_work::map(200,n,|i|if i%7==0 {Err(i as u64)} else {Ok(i as u64)});
        assert_eq!(actual,output);
        let mut zst = Vec::with_capacity(n);
        let mut donor = vec![();n];
        let capacity = donor.capacity();
        zst.append(&mut donor);
        assert_eq!(zst.len(),n);
        assert!(donor.is_empty());
        assert_eq!(donor.capacity(),capacity);
        checks+=1;
    }
    println!("finite Vec append/store/drain checks={checks}; all reached counts; inner Err retained; ZST included");
}
