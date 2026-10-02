67:     let mut oy=vec![B::ZERO;ys.len()];for i in (1..ys.len()).rev(){oy[i]=py[i-1].mul(iy);iy=iy.mul(ys[i]);}oy[0]=iy;
