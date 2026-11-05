fn NHU_coeff0_cut(c1:&[QM31;16],coefficients:&mut [QM31;27],column:usize)->usize{let mut iter=column..16;if let Some(column)=iter.next(){
        coefficients[usize::from(FACTOR_EXPONENTS[column])] =
            mul_tower_basis(c1[column], column & 3);
    
}iter.start}
