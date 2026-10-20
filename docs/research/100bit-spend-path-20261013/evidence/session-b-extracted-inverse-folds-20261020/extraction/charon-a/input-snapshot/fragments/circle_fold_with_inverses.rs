fn circle_fold_with_inverses(alpha:E,a:[E;4],inverse:&[M31;5])->E {
    let [ix,iy,_,_,_]=*inverse;let [a,b,c,d]=a;
    let h0=a.add(b).add(c).add(d).mul_m31(QUARTER);
    let h1=a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
    let h2=a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
    let h3=a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
