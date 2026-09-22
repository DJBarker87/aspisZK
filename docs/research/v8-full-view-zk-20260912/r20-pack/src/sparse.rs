//! Current R18/R19 slot map, unchanged. Caller owns all substantial storage.
use crate::{canonical::Q,whole_dot::Dot};
pub fn slot(i:usize)->usize{128+3*i}
/// Exact G contraction with a whole-dot accumulator per group, not an array
/// of 64 large accumulators. `sums` is exactly 2048 bytes in this representation.
pub fn terminal(coins:&[Q;271],normal:&[Q;16],carry:&[Q;3],high:&[Q;16],sums:&mut[Q;128])->[Q;4]{
    let mut i=0usize;
    for group in 0..64{
        let mut n=Dot::new();let mut c=Dot::new();
        while i<271 && (slot(i)>>4)==group{
            let low=slot(i)&15;n.push(coins[i],normal[low]).unwrap();
            if low<3{c.push(coins[i],carry[low]).unwrap()}i+=1;
        }
        sums[2*group]=n.finish();sums[2*group+1]=c.finish();
    }
    core::array::from_fn(|group|{
        let mut d=Dot::new();for lane in 0..16{
            let j=16*group+lane;let mut bits=j.trailing_ones() as usize;
            let mut value=if j+1<64{sums[2*(j+1)+1]}else{Q::ZERO};
            while bits!=0{bits-=1;let row=j & !((1usize<<(bits+1))-1);value=value.add(sums[2*row+1]).half();}
            d.push(value.add(sums[2*j]),high[lane]).unwrap();
        }
        d.finish().half_pow(8).unwrap()
    })
}
