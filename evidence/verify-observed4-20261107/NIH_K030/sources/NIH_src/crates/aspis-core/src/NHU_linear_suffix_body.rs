fn NHU_linear_suffix(suffix:QM31,weighted:QM31,log:&mut ScalarLog)->(QM31,QM31){
    (
        scalar_cut(suffix,M31(3),log).add(scalar_cut(weighted,M31(22),log)),
        scalar_cut(suffix,M31(275),log).add(scalar_cut(weighted,M31(150),log)),
    )

}
