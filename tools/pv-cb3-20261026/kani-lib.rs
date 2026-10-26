//! No stubs. The source modules are imported verbatim from the pinned snapshot.
#[cfg(kani)]
#[path = "../source/crates/aspis-r1-cost-probe/src/ct_pole.rs"]
mod ct_pole;
#[cfg(kani)]
#[path = "../source/crates/aspis-r1-cost-probe/src/sampler.rs"]
mod sampler;
#[cfg(kani)]
mod reference;
#[cfg(kani)]
mod reference_split;
#[cfg(kani)]
mod source_fragments;
#[cfg(all(kani,not(pv_cb_extract)))]
mod checks {
    use aspis_core::field::{QM31, CM31, M31};
    fn q(w:[u32;4])->QM31 {
        QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}
    }
    #[kani::proof]
    fn pole_equal() {
        let a=q(kani::any());let b=q(kani::any());
        assert_eq!(super::ct_pole::equal(a,b),super::reference::equal(a,b));
    }
    #[kani::proof]
    fn pole_step() {
        let clear:bool=kani::any();let active:bool=kani::any();
        let chi=q(kani::any());let value=q(kani::any());
        assert_eq!(super::ct_pole::keep_clear(clear,active,chi,value),
            clear & !(active & super::reference::equal(chi,value)));
    }
    #[kani::proof]
    #[kani::unwind(4)]
    fn pole_rows2() {
        let words:[[[[u32;4];2];2];2]=kani::any();
        let mut values=[[[QM31::ZERO;2];2];2];
        for row in 0..2 {for side in 0..2 {for v in 0..2 {values[row][side][v]=q(words[row][side][v]);}}}
        let masks:[u16;64]=kani::any();let chi=q(kani::any());
        let n:usize=kani::any();kani::assume(n<=2);
        assert_eq!(super::ct_pole::all_slots_clear(&values[..n],&masks,chi),
            super::reference::all_slots_clear(&values[..n],&masks,chi));
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn gamma() {
        let block:[u8;32]=kani::any();
        assert_eq!(super::sampler::gamma_sample(&block),super::reference::gamma(block));
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn gamma_words_split() {
        let block:[u8;32]=kani::any();
        assert_eq!(super::source_fragments::words(&block),super::reference_split::words(block));
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn gamma_pass_split() {
        let rank:[u32;8]=kani::any();
        assert_eq!(super::source_fragments::pass(rank),super::reference_split::pass(rank));
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn gamma_carry_split() {
        let digits:[u32;8]=kani::any();let add:u32=kani::any();
        assert_eq!(super::source_fragments::carry(digits,add),super::reference_split::carry(digits,add));
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn gamma_split() {
        let block:[u8;32]=kani::any();
        assert_eq!(super::sampler::gamma_sample(&block),super::reference_split::gamma(block));
    }

}
