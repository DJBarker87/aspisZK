    #[inline(always)] pub(crate) fn reduce(mut x:u64)->u32 {
        x=(x & u64::from(P))+(x>>31);
        x=(x & u64::from(P))+(x>>31);
        if x>=u64::from(P) {(x-u64::from(P)) as u32}else{x as u32}
    }
