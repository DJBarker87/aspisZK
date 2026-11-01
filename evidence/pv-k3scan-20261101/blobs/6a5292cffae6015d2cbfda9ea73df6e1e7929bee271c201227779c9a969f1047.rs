#[cfg(kani)]
mod pv_cblib_library_checks {
    use super::*;
    fn empty_reference<T>(v: &Vec<T>) -> bool { v.len() == 0 }
    fn pop_reference<T>(v: &mut Vec<T>) -> Option<T> {
        if v.len() == 0 { None } else { Some(v.remove(v.len() - 1)) }
    }
    fn word(seed: [u32; 4], secure: bool, filled: bool) -> Word {
        if secure {
            let mut v = Vec::new();
            if filled { v.push(QM31 { c0: aspis_core::field::CM31 { a: M31(seed[0]), b: M31(seed[1]) }, c1: aspis_core::field::CM31 { a: M31(seed[2]), b: M31(seed[3]) } }); }
            Word::Secure(v)
        } else {
            let mut v = Vec::new();
            if filled { v.push(M31(seed[0])); }
            Word::Base(v)
        }
    }
    fn same_word(a: &Word, b: &Word) -> bool {
        match (a,b) {
            (Word::Base(x), Word::Base(y)) => x == y,
            (Word::Secure(x), Word::Secure(y)) => x == y,
            _ => false,
        }
    }
    fn same_result(a: &Result<Word, Error>, b: &Result<Word, Error>) -> bool {
        match (a,b) {
            (Ok(x), Ok(y)) => same_word(x,y),
            (Err(x), Err(y)) => x == y,
            _ => false,
        }
    }
    // Every error variant is covered. Error carries no payload.
    fn error(i: u8) -> Error {
        match i {
            0 => Error::IndexOutOfRange, 1 => Error::WrongLength,
            2 => Error::ZeroDenominator, 3 => Error::Allocation,
            4 => Error::NonCanonical, 5 => Error::WrongField,
            6 => Error::InvalidPoints, 7 => Error::QuotientNotInImage,
            8 => Error::RankDeficient, 9 => Error::Parse,
            10 => Error::Semantic, 11 => Error::Schedule,
            12 => Error::Sampler, 13 => Error::Commitment,
            14 => Error::Authentication, 15 => Error::V1, _ => Error::V2,
        }
    }
    fn paired_vectors() -> (Vec<Result<Word, Error>>, Vec<Result<Word, Error>>) {
        let n: usize = kani::any(); kani::assume(n <= 2);
        let mut v = Vec::new(); let mut w = Vec::new();
        for _ in 0..n {
            let good: bool = kani::any(); let seed: [u32;4] = kani::any();
            let secure: bool = kani::any(); let filled: bool = kani::any();
            let i: u8 = kani::any(); kani::assume(i <= 16);
            v.push(if good { Ok(word(seed,secure,filled)) } else { Err(error(i)) });
            w.push(if good { Ok(word(seed,secure,filled)) } else { Err(error(i)) });
        }
        (v,w)
    }
    #[kani::proof]
    fn op35_exact_word() {
        let native = Vec::<Result<Word, Error>>::default();
        let reference = Vec::<Result<Word, Error>>::new();
        assert_eq!(native.len(), reference.len());
        assert_eq!(native.capacity(), reference.capacity());
        assert_eq!(native.len(), 0);
    }
    #[kani::proof]
    #[kani::unwind(4)]
    fn op34_exact_word() {
        let (v,_) = paired_vectors();
        assert_eq!(v.is_empty(), empty_reference(&v));
    }
    #[kani::proof]
    #[kani::unwind(4)]
    fn op33_exact_word() {
        let (mut v,mut w) = paired_vectors();
        let a=v.pop(); let b=pop_reference(&mut w);
        match (a,b) {
            (None,None) => (),
            (Some(x),Some(y)) => assert!(same_result(&x,&y)),
            _ => unreachable!(),
        }
        assert_eq!(v.len(),w.len());
        for i in 0..v.len() { assert!(same_result(&v[i],&w[i])); }
    }
}
