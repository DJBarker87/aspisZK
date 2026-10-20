fn line_fold_with_inverses(alpha:E,a:[E;4],inverse:&[M31;5])->E {
    let [_,_,ix,iy,iz]=*inverse;let half=M31(1073741824);let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(iz));
    let c0=a.sub(b).mul_m31(half.mul(ix));
    let c1=d.sub(c).mul_m31(half.mul(iy));
    let h1=c0.add(c1).mul_m31(half);
    let h3=c0.sub(c1).mul_m31(half.mul(iz));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
