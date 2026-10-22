// Host-only harness. No production source modification.
#[cfg(kani)]
mod nonzero22 {
    use super::*;
    static mut SEED:[u8;32]=[0;32];
    static mut ATTEMPT:u32=0;
    static mut STREAM:u8=0;
    static mut START:u64=0;
    static mut ZEROES:u8=0;
    static mut ANSWER:[u8;32]=[0;32];
    static mut CALLS:u8=0;
    fn hash(parts:&[&[u8]])->[u8;32] {
        unsafe {
            assert_eq!(parts.len(),5);
            assert_eq!(parts[0],b"UNPROVED:R1:SIM:COIN");
            assert_eq!(parts[1],SEED);
            assert_eq!(parts[2],ATTEMPT.to_le_bytes());
            assert_eq!(parts[3],[STREAM]);
            assert_eq!(parts[4],(START+CALLS as u64).to_le_bytes());
            let i=CALLS; CALLS+=1;
            if i<ZEROES {[0;32]} else {ANSWER}
        }
    }
    // Actual shipped loop; all successful prefixes up to the fixed fuel.
    // Prefix size is symbolic; hash checks every frame and counter.
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(aspis_prover::host_hashv,hash)]
    fn within_five() {
        let seed:[u8;32]=kani::any(); let attempt:u32=kani::any();
        let stream:u8=kani::any(); let start:u64=kani::any();
        kani::assume(start<=u64::MAX-5);
        let zeros:u8=kani::any(); kani::assume(zeros<5);
        let answer:[u8;32]=kani::any(); kani::assume(answer!=[0;32]);
        unsafe {SEED=seed;ATTEMPT=attempt;STREAM=stream;START=start;
            ZEROES=zeros;ANSWER=answer;CALLS=0;}
        let mut actual=Coins{seed,attempt,stream,next:start};
        let got=actual.nonzero();
        assert_eq!(got,answer);
        assert_eq!(actual.next,start+zeros as u64+1);
        assert_eq!(actual.seed,seed);assert_eq!(actual.attempt,attempt);assert_eq!(actual.stream,stream);
        assert_eq!(unsafe{CALLS},zeros+1);
    }
}
