fn NHU_pow5_cut(value: QM31,log:&mut PowLog) -> QM31 {
    let square = pow_square(value,log);
    pow_mul(pow_square(square,log),value,log)
}
