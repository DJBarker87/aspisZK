fn NHU_coeff1_cut(mask_only_c1:&[QM31;10],coefficients:&mut [QM31;27],column:usize)->usize{let mut iter=column..10;if let Some(column)=iter.next(){
        coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] =
            mul_tower_basis(mask_only_c1[column], column & 3);
    
}iter.start}
