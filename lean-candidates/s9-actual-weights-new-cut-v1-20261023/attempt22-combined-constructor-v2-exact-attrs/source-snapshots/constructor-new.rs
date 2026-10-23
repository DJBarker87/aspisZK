pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Box<Self>,Error> {
        let points=aspis_core::state_only_prefix::r0::statement_points(alpha);
        let extra=[alpha[8],alpha[9]];
        let mut factors=[[[K::ZERO;4];5];5];
        for k in 0..3 { for d in 0..5 {
            let a=points[k][9-2*TAU[d]]; let b=points[k][8-2*TAU[d]];
            factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
        }}
        for k in 0..2 {
            factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];
            let mut x=double(z[k].x);
            for d in 1..5 {
                let y=double(x); factors[3+k][d]=[K::ONE,x,y,x.mul(y)]; x=double(y);
            }
        }
        Ok(Self::box_from_parts(variant, factors, points, extra))
    }
