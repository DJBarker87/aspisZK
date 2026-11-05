fn NHU_horner_cut(coefficients:&[QM31;27],prepared_linear:PreparedQm31Multiplier,mut shared:QM31,n:usize,log:&mut PreparedLog)->(QM31,usize){let mut iter=(0..n).rev();if let Some(exponent)=iter.next(){
        shared = prepared_cut(prepared_linear,shared,log).add(coefficients[exponent]);
    
}(shared,iter.len())}
