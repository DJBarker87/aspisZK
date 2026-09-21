// Fixed public balanced nodes only; the sparse 256+15 root stays scalar.
// For size n, deg(N_child)<n/2 and deg(D_child)=n/2, so products have
// degree < n: an n-point cyclic convolution has no wraparound.
include!("r17_merge_spectra.rs");

fn scalar_merge(current: &[K], next: &mut [K], start: usize, mid: usize, end: usize, node: usize) {
    next[start..end].fill(K::ZERO);
    for (from, to, other) in [(start, mid, node*2+1), (mid, end, node*2)] {
        let offset = DEN_OFFSETS[other];
        let count = DEN_LENGTHS[other];
        for i in from..to {
            for k in 0..count {
                let at = start + i - from + k;
                next[at] = scalar_fma(next[at], current[i], DENOMINATORS[offset+k]);
            }
        }
    }
}

fn fft_merge(current: &[K], next: &mut [K], start: usize, n: usize, node: usize, work: &mut [CM31]) {
    let offset = MERGE_OFFSETS[node];
    assert_ne!(offset, usize::MAX);
    let (left, rest) = work.split_at_mut(n);
    let right = &mut rest[..n];
    for component in 0..2 {
        left.fill(CM31::ZERO);
        right.fill(CM31::ZERO);
        for i in 0..n/2 {
            let a = current[start+i];
            let b = current[start+n/2+i];
            left[i] = if component == 0 { a.c0 } else { a.c1 };
            right[i] = if component == 0 { b.c0 } else { b.c1 };
        }
        fft(left, false);
        fft(right, false);
        for i in 0..n {
            left[i] = left[i].mul(MERGE_SPECTRA[offset+i])
                .add(right[i].mul(MERGE_SPECTRA[offset+n+i]));
        }
        fft(left, true);
        for i in 0..n {
            if component == 0 { next[start+i].c0 = left[i]; }
            else { next[start+i].c1 = left[i]; }
        }
    }
}

#[cfg(not(performance_sbf))]
fn check_hybrid() {
    for n in [64usize,128,256,2048] {
        let root = ROOTS[2048/n];
        assert_eq!(root.pow(n as u64),CM31::ONE);
        assert_ne!(root.pow((n/2) as u64),CM31::ONE);
        let shift = 31-n.trailing_zeros();
        assert_eq!(M31(n as u32).mul(M31(1<<shift)),M31::ONE);
        let mut a: Vec<_> = (0..n).map(|i| CM31::new(M31((i*97+7) as u32),M31(2147483646))).collect();
        let original = a.clone();
        fft(&mut a,false); fft(&mut a,true);
        assert_eq!(a,original);
    }
    let tag=K { c0: CM31::new(M31(3),M31(5)), c1: CM31::new(M31(7),M31(11)) };
    let mut current=vec![K::ZERO;271];
    let mut actual=vec![tag;271];
    let mut expected=vec![tag;271];
    let mut work=vec![CM31::ONE;2048];
    let mut tested=0;
    for n in [64usize,128,256] {
        for start in (0..271).step_by(n) {
            if start+n>271 { continue; }
            let node=512/n+start/n;
            // Independent inverse check binds every spectrum to its exact opposite denominator.
            for (side,other) in [(0,node*2+1),(1,node*2)] {
                let off=MERGE_OFFSETS[node]+side*n;
                let mut spectrum=MERGE_SPECTRA[off..off+n].to_vec();
                fft(&mut spectrum,true);
                for i in 0..n {
                    assert_eq!(spectrum[i],if i<DEN_LENGTHS[other] {
                        CM31::from_m31(DENOMINATORS[DEN_OFFSETS[other]+i])
                    } else {CM31::ZERO});
                }
            }
            // Every basis position, plus zero, maximum limbs, and eight full-limb vectors.
            for case in 0..n+10 {
                current.fill(K::ZERO);
                for i in 0..n {
                    current[start+i]=if case<n { if i==case {tag} else {K::ZERO} }
                        else if case==n {K::ZERO}
                        else if case==n+1 {let m=M31(2147483646); K{c0:CM31::new(m,m),c1:CM31::new(m,m)}}
                        else {
                            let seed=(case as u64*0x9e3779b9)^(i as u64*0x85ebca6b);
                            let limb=|k| M31::reduce_u64(seed.wrapping_mul(k));
                            K {c0:CM31::new(limb(17),limb(31)),c1:CM31::new(limb(97),limb(109))}
                        };
                }
                actual.fill(tag); expected.fill(tag);
                fft_merge(&current,&mut actual,start,n,node,&mut work);
                scalar_merge(&current,&mut expected,start,start+n/2,start+n,node);
                assert_eq!(actual,expected,"node {node}, case {case}");
                tested+=1;
            }
        }
    }
    assert_eq!(tested,838);
    println!("PASS: short-transform root order/normalization/roundtrips, all 14 denominator spectra, 838 individual merge controls (all 768 basis positions)");
}
