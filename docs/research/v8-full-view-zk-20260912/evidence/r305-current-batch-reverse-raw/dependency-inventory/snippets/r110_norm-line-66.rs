66:     let mut ox=vec![B::ZERO;xs.len()];for i in (1..xs.len()).rev(){ox[i]=px[i-1].mul(ix);ix=ix.mul(xs[i]);}ox[0]=ix;
