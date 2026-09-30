// Same bounded partial-product affine kernel, on private canonical operands.
impl Q{
    #[inline(always)]
    pub fn affine3(constant:Self,left:&[Self;3],right:[Self;3])->Self{
        let mut sums=constant.0.map(u64::from);
        for i in 0..3{
            let raw=left[i].raw(right[i]);
            for j in 0..4{sums[j]=sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31));}
        }
        // Three partials <2^34 each plus a canonical constant: no u64 wrap.
        Self(sums.map(reduce))
    }
}
