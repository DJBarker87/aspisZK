// Natural coefficients -> bit-reversed spectrum (DIF), then inverse DIT
// consumes that spectrum directly. Fixed spectra use the same permutation.
include!("r17_aligned_spectra.rs");

#[inline(always)]
fn dif_butterfly(u: CM31, v: CM31, w: CM31) -> (CM31,CM31) {
    const P: u64=2147483647;
    const P2: u64=P*P;
    // 0 < x,y <= 2P-1; every product < 2P². Both padded expressions,
    // including the real addition before subtraction, are below 4P² < 2^64.
    let x=u.a.0 as u64+P-v.a.0 as u64;
    let y=u.b.0 as u64+P-v.b.0 as u64;
    let real=x*w.a.0 as u64+2*P2-y*w.b.0 as u64;
    let imag=x*w.b.0 as u64+y*w.a.0 as u64;
    (u.add(v),CM31::new(M31::reduce_u64(real),M31::reduce_u64(imag)))
}

fn aligned_fixed<const N:usize,const INVERSE:bool>(a:&mut[CM31]) {
    assert_eq!(a.len(),N);
    let mut len=if INVERSE {2} else {N};
    while len>=2 && len<=N {
        let step=2048/len;
        for start in (0..N).step_by(len) {
            for k in 0..len/2 {
                let index=if INVERSE {(2048-k*step)&2047} else {k*step};
                let u=a[start+k];let v=a[start+k+len/2];
                let (left,right)=if index==0 {(u.add(v),u.sub(v))}
                    else if INVERSE {
                        if index==1536 {quarter_turn(u,v,true)} else {butterfly(u,v,ROOTS[index])}
                    } else if index==512 {
                        (u.add(v),CM31::new(u.b.sub(v.b),v.a.sub(u.a)))
                    } else {dif_butterfly(u,v,ROOTS[index])};
                a[start+k]=left;a[start+k+len/2]=right;
            }
        }
        if INVERSE {len*=2;} else {len/=2;}
    }
    if INVERSE {
        let shift=(31-N.trailing_zeros()) as u8;
        for x in a {*x=CM31::new(x.a.mul_pow2(shift),x.b.mul_pow2(shift));}
    }
}

fn aligned_fft(a:&mut[CM31],inverse:bool) {
    match (a.len(),inverse) {
        (64,false)=>aligned_fixed::<64,false>(a),
        (64,true)=>aligned_fixed::<64,true>(a),
        (128,false)=>aligned_fixed::<128,false>(a),
        (128,true)=>aligned_fixed::<128,true>(a),
        (256,false)=>aligned_fixed::<256,false>(a),
        (256,true)=>aligned_fixed::<256,true>(a),
        (2048,false)=>aligned_fixed::<2048,false>(a),
        (2048,true)=>aligned_fixed::<2048,true>(a),
        _=>panic!("unsupported aligned FFT length"),
    }
}

#[cfg(not(performance_sbf))]
fn check_aligned_fft() {
    let limbs=[0u32,1,2,2147483645,2147483646];
    for code in 0..15625usize {
        let mut n=code;let mut z=[0;6];
        for x in &mut z {*x=limbs[n%5];n/=5;}
        let u=CM31::new(M31(z[0]),M31(z[1]));
        let v=CM31::new(M31(z[2]),M31(z[3]));
        let w=CM31::new(M31(z[4]),M31(z[5]));
        assert_eq!(dif_butterfly(u,v,w),(u.add(v),u.sub(v).mul(w)));
        let p=2147483647u64;
        let x=(z[0] as u64).checked_add(p).unwrap().checked_sub(z[2] as u64).unwrap();
        let y=(z[1] as u64).checked_add(p).unwrap().checked_sub(z[3] as u64).unwrap();
        let real=x.checked_mul(z[4] as u64).unwrap().checked_add(2*p*p).unwrap()
            .checked_sub(y.checked_mul(z[5] as u64).unwrap()).unwrap();
        let imag=x.checked_mul(z[5] as u64).unwrap().checked_add(y.checked_mul(z[4] as u64).unwrap()).unwrap();
        assert!(real<4*p*p && imag<4*p*p);
    }
    let rev=|i:usize,n:usize| i.reverse_bits()>>(usize::BITS-n.trailing_zeros());
    for i in 0..2048 {assert_eq!(ALIGNED_INVERSE[i],INVERSE_SPECTRUM[rev(i,2048)]);}
    for n in [64usize,128,256] {
        for start in (0..271).step_by(n) {
            if start+n>271 {continue;}
            let offset=MERGE_OFFSETS[512/n+start/n];
            for side in 0..2 {for i in 0..n {
                assert_eq!(ALIGNED_MERGE[offset+side*n+i],MERGE_SPECTRA[offset+side*n+rev(i,n)]);
            }}
        }
    }
    for n in [64usize,128,256,2048] {
        for case in 0..5 {
            let input:Vec<_>=(0..n).map(|i| match case {
                0=>CM31::ZERO,
                1=>CM31::new(M31(2147483646),M31(2147483646)),
                2=>if i==n-1 {CM31::new(M31(3),M31(7))} else {CM31::ZERO},
                3=>CM31::new(M31((i*17+9) as u32),M31((i*93+3) as u32)),
                _=>CM31::new(M31::reduce_u64(i as u64*0x9e3779b9),M31::reduce_u64(i as u64*0x85ebca6b+71))
            }).collect();
            let mut expected=input.clone();fft(&mut expected,false);
            let mut actual=input.clone();aligned_fft(&mut actual,false);
            for i in 0..n {assert_eq!(actual[i],expected[rev(i,n)]);}
            aligned_fft(&mut actual,true);assert_eq!(actual,input);
            // Independent inverse input, not only inverse-after-forward.
            let mut inverse:Vec<_>=(0..n).map(|i|input[rev(i,n)]).collect();
            expected=input.clone();fft(&mut expected,true);
            aligned_fft(&mut inverse,true);assert_eq!(inverse,expected);
        }
    }
    println!("PASS: 15625 DIF boundary tuples and checked intermediates; all 3584 reordered constants; 20 forward, 20 independent inverse, 20 roundtrip comparisons");
}
