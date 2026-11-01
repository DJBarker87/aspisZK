//! Differential test: the extraction-friendly Poseidon copy (refine/poseidon)
//! against the production permutation permute_optimized_with_trace.
use aspis_core::field::{M31, P};
use aspis_r0_poseidon_copy as pc;
use aspis_statement::poseidon2::{permute, permute_optimized_with_trace};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn m31(&mut self) -> u32 {
        (self.next() % P as u64) as u32
    }
}

fn prod_rounds(pre: &[u32; 16], absorb: &[u32; 16]) -> ([[u32; 16]; 11], [u32; 16]) {
    let mut state: [M31; 16] = core::array::from_fn(|i| M31(pre[i]).add(M31(if i < 8 { absorb[i] } else { 0 })));
    let mut out = [[0u32; 16]; 11];
    permute_optimized_with_trace(&mut state, |t| {
        if t.round & 1 == 1 {
            out[usize::from(t.round) / 2] = core::array::from_fn(|i| t.output[i].0);
        }
    });
    (out, core::array::from_fn(|i| state[i].0))
}

#[test]
fn perm_rounds_match() {
    let mut rng = Rng(0x0f1e_2d3c_4b5a_6978);
    for n in 0..100_000u64 {
        let pre: [u32; 16] = core::array::from_fn(|i| if n < 3 { [0, 1, P - 1][n as usize] } else { let _ = i; rng.m31() });
        let mut absorb: [u32; 16] = core::array::from_fn(|_| rng.m31());
        for i in 8..16 {
            absorb[i] = 0;
        }
        let (want, fin) = prod_rounds(&pre, &absorb);
        let got = pc::perm_rounds(&pre, &absorb);
        assert_eq!(got, want);
        assert_eq!(got[10], fin);
    }
    println!("perm_rounds_match: 100000 states");
}

#[test]
fn canonical_permute_matches() {
    let mut rng = Rng(0x1357_2468_aceb_dfca);
    for _ in 0..50_000u64 {
        let s: [u32; 16] = core::array::from_fn(|_| rng.m31());
        let mut st: [M31; 16] = core::array::from_fn(|i| M31(s[i]));
        permute(&mut st);
        let zero = [0u32; 16];
        let got = pc::perm_rounds(&s, &zero);
        assert_eq!(got[10], core::array::from_fn::<u32, 16, _>(|i| st[i].0));
    }
    println!("canonical_permute_matches: 50000 states");
}

#[test]
fn field_ops_match() {
    let mut rng = Rng(0x9999_1111_7777_3333);
    for i in 0..1_000_000u64 {
        let (a, b) = if i < 9 { ([0, 1, P - 1][(i % 3) as usize], [0, 1, P - 1][(i / 3) as usize]) } else { (rng.m31(), rng.m31()) };
        assert_eq!(M31(a).add(M31(b)).0, pc::m31_add(a, b));
        assert_eq!(M31(a).mul(M31(b)).0, pc::m31_mul(a, b));
    }
    println!("field_ops_match: 1000000 pairs");
}
