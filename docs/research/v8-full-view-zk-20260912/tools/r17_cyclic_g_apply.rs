// UNCOMPILED integration draft: include inside the R24-derived r17_fast_g.rs.
// It reuses K, M31, CM31, DEN_* tables, scalar_merge, fft_merge and fft.
// Add (1024,false/true) to the retained fft_fixed dispatch (NOT rejected DIF).
// Keep old apply as a HOST reference. Do not delete old tables needed by it.
include!("r17_cyclic_tables.rs");

fn cyclic_numerator_into(coins: &[K; 271], out: &mut [K; 1024], work: &mut [CM31]) {
    assert!(work.len() >= 512); // largest retained short merge uses two 256 arrays
    let (first, rest) = out.split_at_mut(271);
    let (second, _) = rest.split_at_mut(271);
    let (mut current, mut next) = (first, second);
    for i in 0..271 { current[i] = coins[i].mul_m31(COIN_SCALE_1024[i]); }
    let mut swapped = false;
    let mut size = 2;
    while size <= 512 {
        for start in (0..271).step_by(size) {
            let mid = core::cmp::min(start + size/2, 271);
            let end = core::cmp::min(start + size, 271);
            if mid == end {
                next[start..end].copy_from_slice(&current[start..end]);
                continue;
            }
            let node = 512/size + start/size;
            if matches!(size, 64 | 128 | 256) && end-start == size {
                fft_merge(current, next, start, size, node, work);
            } else {
                scalar_merge(current, next, start, mid, end, node);
            }
        }
        core::mem::swap(&mut current, &mut next);
        swapped = !swapped;
        size *= 2;
    }
    if swapped { next.copy_from_slice(current); }
}

pub(super) fn apply_cyclic_1024(coins: &[K; 271], out: &mut [K; 1024]) {
    // Compute BEFORE numerator/output overwrite. This is the missing Fourier
    // value at X=1, where D(1)=0. No division by zero or challenge inversion.
    let mut dc = K::ZERO;
    for i in 0..271 { dc = dc.add(coins[i].mul_m31(DC_WEIGHT_1024[i])); }
    let mut work = vec![CM31::ZERO; 1024];
    cyclic_numerator_into(coins, out, &mut work);
    for component in 0..2 {
        work.fill(CM31::ZERO);
        for i in 0..271 {
            work[i] = if component == 0 { out[i].c0 } else { out[i].c1 };
        }
        fft(&mut work, false);
        work[0] = if component == 0 { dc.c0 } else { dc.c1 };
        for i in 1..1024 { work[i] = work[i].mul(INV_DEN_1024[i]); }
        fft(&mut work, true);
        for j in 0..1024 {
            if component == 0 { out[j].c0 = work[j]; }
            else { out[j].c1 = work[j]; }
        }
    }
}
