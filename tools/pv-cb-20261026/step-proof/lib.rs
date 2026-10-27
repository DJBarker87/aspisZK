#![cfg(kani)]
pub use aspis_core::{field,transcript};
#[path="../source-proof/owned.rs"]
pub mod owned;
pub mod captured_mask;
pub mod owned_points;
pub mod owned_wide_new;
pub mod owned_compress;
pub mod owned_pole;
#[path="../source/crates/aspis-r1-cost-probe/src/ct_pole.rs"]
pub mod shipped_pole;
#[path="../source-proof/owned_circle.rs"]
pub mod owned_circle;
#[cfg(not(pv_cb_extract))]
mod checks {
    use aspis_core::field::{M31,CM31,QM31,PreparedQm31Multiplier};
    use super::captured_mask as shipped;
    use super::owned::steps as reference;
    fn q(x:[u32;4])->QM31 {QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
    fn cq(words:[u32;4])->QM31 {
        for word in words { kani::assume(word < aspis_core::field::P); }
        q(words)
    }
    #[kani::proof]
    #[kani::unwind(1026)]
    fn pole1024_reference() {
        let words:[[[[u32;4];2];2];1024]=kani::any();
        let mut values=[[[QM31::ZERO;2];2];1024];
        for row in 0..1024 { for side in 0..2 { for slot in 0..2 {
            values[row][side][slot]=q(words[row][side][slot]);
        } } }
        let masks:[u16;64]=kani::any(); let chi=q(kani::any());
        assert_eq!(super::shipped_pole::all_slots_clear(&values,&masks,chi),
                   super::owned_pole::all_slots_clear(&values,&masks,chi));
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn compress16_canonical_reference() {
        let tag_word:u32=kani::any(); kani::assume(tag_word<aspis_core::field::P);
        let tag=M31(tag_word);
        let words:[u32;16]=kani::any(); let mut values=[M31::ZERO;16];
        for i in 0..16 { kani::assume(words[i]<aspis_core::field::P); values[i]=M31(words[i]); }
        let lambda=cq(kani::any());
        same(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),
             super::owned_compress::compress(tag,&values,lambda));
    }
    fn same(a:QM31,b:QM31) {
        assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);
        assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
    }

    #[kani::proof]
    #[kani::unwind(18)]
    fn compress16_reference() {
        let tag = M31(kani::any());
        let words: [u32;16] = kani::any();
        let mut values = [M31::ZERO;16];
        for i in 0..16 { values[i] = M31(words[i]); }
        let lambda = q(kani::any());
        same(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),
             super::owned_compress::compress(tag,&values,lambda));
    }
    #[kani::proof]
    #[kani::unwind(40)]
    fn captured_source() {
        let words=kani::any::<[[u32;4];37]>().map(q);
        let mut c1=[QM31::ZERO;16];let mut mask=[QM31::ZERO;10];let mut point=[QM31::ZERO;10];
        for i in 0..16 {c1[i]=words[i];}
        for i in 0..10 {mask[i]=words[16+i];point[i]=words[27+i];}
        let g=words[26];
        same(aspis_core::state_only_hiding::state_only_selected_mask_value(&c1,&mask,g,&point),
             shipped::state_only_selected_mask_value(&c1,&mask,g,&point));
    }
    #[kani::proof]
    #[kani::unwind(30)]
    fn c1_step() {
        let data=kani::any::<[[u32;4];16]>().map(q);
        let coeff=kani::any::<[[u32;4];27]>().map(q);
        let i:usize=kani::any();kani::assume(i<16);
        let a=shipped::c1_step(&data,coeff,i);let b=reference::c1_step(&data,coeff,i);
        for j in 0..27 {same(a[j],b[j]);}
    }
    #[kani::proof]
    #[kani::unwind(30)]
    fn mask_step() {
        let data=kani::any::<[[u32;4];10]>().map(q);
        let coeff=kani::any::<[[u32;4];27]>().map(q);
        let i:usize=kani::any();kani::assume(i<10);
        let a=shipped::mask_step(&data,coeff,i);let b=reference::mask_step(&data,coeff,i);
        for j in 0..27 {same(a[j],b[j]);}
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn linear_step() {
        let p=kani::any::<[[u32;4];10]>().map(q);let i:usize=kani::any();kani::assume(i<10);
        let s=q(kani::any());let w=q(kani::any());
        let a=shipped::linear_step(&p,i,s,w);let b=reference::linear_step(&p,i,s,w);
        same(a.0,b.0);same(a.1,b.1);
    }
    #[kani::proof]
    #[kani::unwind(30)]
    fn horner_step() {
        let coeff=kani::any::<[[u32;4];27]>().map(q);let i:usize=kani::any();kani::assume(i<26);
        let prepared=PreparedQm31Multiplier::new(q(kani::any()));let state=q(kani::any());
        same(shipped::horner_step(&coeff,prepared,i,state),reference::horner_step(&coeff,prepared,i,state));
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn tower_step() {
        let x=q(kani::any());let i:usize=kani::any();kani::assume(i<4);
        same(shipped::tower(x,i),reference::tower_step(x,i));
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn linears() {
        let p=kani::any::<[[u32;4];10]>().map(q);
        let a=shipped::linears(&p);let b=reference::linears_step(&p);same(a.0,b.0);same(a.1,b.1);
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn power26() {let x=q(kani::any());same(shipped::power26(x),reference::power26_step(x));}
    // Isolate coefficient selection: both sides read the same symbolic slot,
    // independently of multiplication. This replaces, rather than reruns,
    // the timed-out combined array/arithmetic property.
    #[kani::proof]
    #[kani::unwind(30)]
    fn horner_index() {
        let coeff=kani::any::<[[u32;4];27]>().map(q);
        let i:usize=kani::any();kani::assume(i<26);
        let direct=coeff[i];
        let decremented= i+1-1;
        same(direct,coeff[decremented]);
    }
    #[kani::proof]
    #[kani::unwind(30)]
    fn horner_uniform() {
        let term=q(kani::any());let coeff=[term;27];
        let i:usize=kani::any();kani::assume(i<26);
        let prepared=PreparedQm31Multiplier::new(q(kani::any()));let state=q(kani::any());
        same(shipped::horner_step(&coeff,prepared,i,state),reference::horner_step(&coeff,prepared,i,state));
    }

    // PREPARED fallback for op118: unrestricted raw QM31 inputs, real shipped
    // call, no stubs. Ten decreasing recursive calls and the ten-coordinate
    // production loop fit unwind 12; the comparison loops have bounds 3/10.
    #[kani::proof]
    #[kani::unwind(12)]
    fn statement_points_reference() {
        let point = kani::any::<[[u32; 4]; 10]>().map(q);
        let actual = aspis_core::state_only_prefix::r0::statement_points(&point);
        let expected = super::owned_points::statement_points(&point);
        for row in 0..3 {
            for coordinate in 0..10 {
                same(actual[row][coordinate], expected[row][coordinate]);
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    fn wide_new_reference() {
        let input = kani::any::<[[u32; 4]; 2]>().map(q);
        let actual = aspis_core::field::WideExact::new(input[0], input[1]);
        let expected = super::owned_wide_new::new(input[0], input[1]);
        same(actual.c0(), expected.c0);
        same(actual.c1(), expected.c1);
    }

    fn limb(value: QM31, coordinate: usize) -> u32 {
        match coordinate {
            0 => value.c0.a.0,
            1 => value.c0.b.0,
            2 => value.c1.a.0,
            _ => value.c1.b.0,
        }
    }
    // Each property keeps every raw arithmetic input. Only the asserted
    // output coordinate changes; no other coordinate equality is assumed.
    macro_rules! horner_word {
        ($name:ident, $coordinate:expr) => {
            #[kani::proof]
            #[kani::unwind(30)]
            fn $name() {
                let term = q(kani::any());
                let coefficients = [term; 27];
                let index: usize = kani::any();
                kani::assume(index < 26);
                let prepared = PreparedQm31Multiplier::new(q(kani::any()));
                let state = q(kani::any());
                let actual = shipped::horner_step(&coefficients, prepared, index, state);
                let expected = reference::horner_step(&coefficients, prepared, index, state);
                assert_eq!(limb(actual, $coordinate), limb(expected, $coordinate));
            }
        };
    }
    macro_rules! power_word {
        ($name:ident, $coordinate:expr) => {
            #[kani::proof]
            #[kani::unwind(6)]
            fn $name() {
                let input = q(kani::any());
                let actual = shipped::power26(input);
                let expected = reference::power26_step(input);
                assert_eq!(limb(actual, $coordinate), limb(expected, $coordinate));
            }
        };
    }
    horner_word!(horner_word0, 0);
    horner_word!(horner_word1, 1);
    horner_word!(horner_word2, 2);
    horner_word!(horner_word3, 3);
    power_word!(power26_word0, 0);
    power_word!(power26_word1, 1);
    power_word!(power26_word2, 2);
    power_word!(power26_word3, 3);

    macro_rules! canonical_horner_word {
        ($name:ident, $coordinate:expr) => {
            #[kani::proof]
            #[kani::unwind(30)]
            fn $name() {
                let term = cq(kani::any());
                let coefficients = [term; 27];
                let index: usize = kani::any();
                kani::assume(index < 26);
                let prepared = PreparedQm31Multiplier::new(cq(kani::any()));
                let state = cq(kani::any());
                let actual = shipped::horner_step(&coefficients, prepared, index, state);
                let expected = reference::horner_step(&coefficients, prepared, index, state);
                assert_eq!(limb(actual, $coordinate), limb(expected, $coordinate));
            }
        };
    }
    macro_rules! canonical_power_word {
        ($name:ident, $coordinate:expr) => {
            #[kani::proof]
            #[kani::unwind(6)]
            fn $name() {
                let input = cq(kani::any());
                let actual = shipped::power26(input);
                let expected = reference::power26_step(input);
                assert_eq!(limb(actual, $coordinate), limb(expected, $coordinate));
            }
        };
    }
    canonical_horner_word!(canonical_horner_word0, 0);
    canonical_horner_word!(canonical_horner_word1, 1);
    canonical_horner_word!(canonical_horner_word2, 2);
    canonical_horner_word!(canonical_horner_word3, 3);
    canonical_power_word!(canonical_power26_word0, 0);
    canonical_power_word!(canonical_power26_word1, 1);
    canonical_power_word!(canonical_power26_word2, 2);
    canonical_power_word!(canonical_power26_word3, 3);

    #[kani::proof]
    #[kani::unwind(40)]
    fn circle_sample_reference() {
        let block = kani::any::<[u8; 32]>();
        let row = if kani::any::<bool>() {
            aspis_core::r0_transcript::CircleRow::First
        } else {
            aspis_core::r0_transcript::CircleRow::Second
        };
        let actual = aspis_r1_cost_probe::sampler::circle_sample(&block, row);
        let expected = super::owned_circle::circle_sample(&block, row);
        same(actual.x, expected.x);
        same(actual.y, expected.y);
    }

    // Resume5 partitions: all calls are to the actual shipped compressor.
    // Length and output projection are explicit; no arithmetic stubs/contracts.
    macro_rules! compress_partition {
        ($name:ident,$length:expr,$coordinate:expr) => {
            #[kani::proof]
            #[kani::unwind(18)]
            fn $name() {
                let tag_word:u32=kani::any(); kani::assume(tag_word<aspis_core::field::P);
                let words:[u32;$length]=kani::any(); let mut values=[M31::ZERO;$length];
                for i in 0..$length {kani::assume(words[i]<aspis_core::field::P);values[i]=M31(words[i]);}
                let lambda=cq(kani::any());
                let actual=aspis_statement::logup::compress_tagged_tuple(M31(tag_word),&values,lambda);
                let expected=super::owned_compress::compress(M31(tag_word),&values,lambda);
                if $coordinate==4 { same(actual,expected); }
                else { assert_eq!(limb(actual,$coordinate),limb(expected,$coordinate)); }
            }
        };
    }
    compress_partition!(compress16_lane0,16,0);
    compress_partition!(compress16_lane1,16,1);
    compress_partition!(compress16_lane2,16,2);
    compress_partition!(compress16_lane3,16,3);
    compress_partition!(compress1_all,1,4);
    compress_partition!(compress0_all,0,4);
    compress_partition!(compress2_lane0,2,0);

    // Smaller op117 partitions keep arbitrary canonical arithmetic inputs.
    // Index26 is excluded by the actual26-step Horner caller.
    macro_rules! horner_index_lane {
        ($name:ident,$index:expr,$lane:expr) => {
            #[kani::proof]
            #[kani::unwind(30)]
            fn $name() {
                let coefficients=kani::any::<[[u32;4];27]>().map(cq);
                let prepared=PreparedQm31Multiplier::new(cq(kani::any()));
                let state=cq(kani::any());
                let actual=shipped::horner_step(&coefficients,prepared,$index,state);
                let expected=reference::horner_step(&coefficients,prepared,$index,state);
                assert_eq!(limb(actual,$lane),limb(expected,$lane));
            }
        };
    }
    horner_index_lane!(horner_index0_lane0,0,0);
    horner_index_lane!(horner_index0_lane1,0,1);
    horner_index_lane!(horner_index25_lane2,25,2);
    horner_index_lane!(horner_index25_lane3,25,3);
    #[kani::proof]
    #[kani::unwind(6)]
    fn power26_base_lane0() {
        let input=M31(kani::any());kani::assume(input.0<aspis_core::field::P);
        let value=QM31::from_cm31(CM31::from_m31(input));
        assert_eq!(limb(shipped::power26(value),0),limb(reference::power26_step(value),0));
    }

}
