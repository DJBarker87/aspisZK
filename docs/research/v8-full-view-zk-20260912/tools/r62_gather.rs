// Tables generated from the pinned T163 support; no change of basis.
#[inline(never)]
fn r62_gather(delta:&[K],hb:&[K],scratch:&mut[K],out:&mut[K;19]) {
    assert_eq!(delta.len(),163);assert!(hb.len()>=128);assert!(scratch.len()>=60);
    let (left,right)=scratch[..60].split_at_mut(30);
    for low in 0..19 {
        let start=R62_ENDS[low];let end=R62_ENDS[low+1];let n=end-start;
        for j in 0..n {
            left[j]=delta[R62_ROWS[start+j]];
            right[j]=hb[R62_GROUPS[start+j]];
        }
        out[low]=corelib::field::qm31_dot(&left[..n],&right[..n]);
    }
}

#[cfg(not(target_os="solana"))]
pub(super) fn r62_gather_check(x:&[K;24]) {
    let delta:[K;163]=core::array::from_fn(|i|x[i%24]);
    let hb:[K;128]=core::array::from_fn(|i|x[(i+11)%24]);
    let mut actual=[K::ONE;19];let mut scratch=[K::ONE;60];
    r62_gather(&delta,&hb,&mut scratch,&mut actual);
    let mut expected=[K::ZERO;19];
    for i in 0..163 {
        let row=SUPPORT[i];let group=row>>4;let low=row&15;let value=delta[i];
        expected[low]=expected[low].add(value.mul(hb[group]));
        if low<3 {expected[16+low]=expected[16+low].add(value.mul(hb[64+group]));}
    }
    assert_eq!(actual,expected);
}
