fn NHU_power26_cut(value:QM31,log:&mut PowerLog)->QM31{
    let x2 = square_cut(value, log);
    let x4 = square_cut(x2, log);
    let x8 = square_cut(x4, log);
    let x16 = square_cut(x8, log);
    { let x24 = multiply_cut(x16,x8,log); multiply_cut(x24,x2,log) }
}
