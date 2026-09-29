// Included inside r19_channel_ordinary, after the retained scalar implementation.
// terminal_scalar leaves its verifier-derived high/final adjoint at 403..531.
// No prover-provided cache is accepted. The caller invokes this immediately
// after terminal_scalar, before reusing the workspace for any other purpose.
#[inline(never)]
pub(super) fn r81_sparse_scalar_after_ordinary(
    coins:&[K], workspace:&[K], kernel:&r17_weighted_groups::Kernel,
)->K {
    assert!(coins.len()>=271 && workspace.len()>=531);
    let hb=&workspace[403..531];
    let (normal,carry,_)=kernel.geometry_parts();
    let mut values=[K::ZERO;19];
    let mut left=[K::ZERO;17];let mut right=[K::ZERO;17];
    for low in 0..16 {
        // 3*11 = 1 mod 16; selected code row is exactly 128+3*i.
        let start=(11*low)%16;let mut n=0;let mut i=start;
        while i<271 {
            left[n]=coins[i];right[n]=hb[(128+3*i)>>4];
            n+=1;i+=16;
        }
        values[low]=corelib::field::r25_checked_dot(&left[..n],&right[..n])
            .expect("canonical sparse normal operands");
        if low<3 {
            for j in 0..n {right[j]=hb[64+((128+3*(start+16*j))>>4)];}
            values[16+low]=corelib::field::r25_checked_dot(&left[..n],&right[..n])
                .expect("canonical sparse carry operands");
        }
    }
    scalar_low(normal,carry,&values)
}

#[cfg(not(target_os="solana"))]
pub(super) fn r81_sparse_scalar_check(x:&[K;24],case:usize) {
    let audit=core::array::from_fn(|i|x[i]);
    let abc=core::array::from_fn(|i|x[11+i]);
    let alpha=core::array::from_fn(|i|x[14+i]);
    let finals=core::array::from_fn(|i|x[19+i]);
    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
    let mut workspace=vec![K::ONE;531];
    terminal_scalar(&audit,abc,alpha,x[18],&finals,&mut workspace,&kernel);
    let (_,_,high)=kernel.geometry_parts();let mut independent_hb=[K::ZERO;128];
    scalar_geometry(high,&finals,&mut independent_hb);
    assert_eq!(&workspace[403..531],&independent_hb,"ordinary cache postcondition");
    // Independent retained coordinate kernel, not the new low-group gather.
    let weights:Vec<K>=(0..271).map(|i|corelib::field::qm31_sum_products4(
        kernel.coordinate(128+3*i),finals)).collect();
    let mut coins:Vec<K>=(0..271).map(|i|x[(7*i+5)%24]).collect();
    let expected=coins.iter().zip(&weights).fold(K::ZERO,|s,(&a,&b)|s.add(a.mul(b)));
    assert_eq!(r81_sparse_scalar_after_ordinary(&coins,&workspace,&kernel),expected,
        "sparse arbitrary case {case}");
    if case==3 {
        for i in 0..271 {
            coins.fill(K::ZERO);coins[i]=K::ONE;
            assert_eq!(r81_sparse_scalar_after_ordinary(&coins,&workspace,&kernel),weights[i],
                "sparse selected basis {i}");
        }
    }
}
