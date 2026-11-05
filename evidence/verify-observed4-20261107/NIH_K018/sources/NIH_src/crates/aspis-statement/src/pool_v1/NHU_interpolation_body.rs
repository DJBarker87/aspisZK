fn NHU_interpolation_cut(
    weight0: u32,
    weight1: u32,
    weight2: u32,
    constant0: u32,
    constant1: u32,
    constant2: u32,
log:&mut InterpolationLog) -> M31 {
    raw_reduce(
        raw_product(weight0,constant0,log)
            + raw_product(weight1,constant1,log)
            + raw_product(weight2,constant2,log),
    log)
}
