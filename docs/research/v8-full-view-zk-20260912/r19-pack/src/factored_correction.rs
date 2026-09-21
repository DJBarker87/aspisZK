//! Uncompiled T163 correction candidate. Same signed linear operator.
//! Run check_stage_inventory.py. Caller owns all scratch; do not stack-allocate it.
use super::corelib::field::{QM31 as K,qm31_sum_products4};
include!("correction_tables.rs");
/// ONE tensor w[row]=low[row%16]*high[row/16], not the whole A/E expression.
/// All A tensors and E must still contribute. Scratch needs 240 QM31 entries.
#[inline(never)]
pub fn evaluate(low:&[K;16],high:&[K;64],normal:&[K;16],carry:&[K;3],
    terminal_high:&[K;16],scratch:&mut[K])->[K;4]{
    assert!(scratch.len()>=240);
    let(cache,groups)=scratch.split_at_mut(112);groups[..128].fill(K::ZERO);
    for(i,p)in NORMAL_PAIRS.iter().enumerate(){cache[i]=low[p[0]as usize].mul(normal[p[1]as usize]);}
    for(i,p)in CARRY_PAIRS.iter().enumerate(){cache[100+i]=low[p[0]as usize].mul(carry[p[1]as usize]);}
    for b in NORMAL_BLOCKS{
        let mut v=K::ZERO;
        for t in &NORMAL_TERMS[b[2]as usize..b[3]as usize]{let c=cache[t[0]as usize];v=if t[1]>0{v.add(c)}else{v.sub(c)};}
        let j=2*b[1]as usize;groups[j]=groups[j].add(high[b[0]as usize].mul(v));
    }
    for b in CARRY_BLOCKS{
        let mut v=K::ZERO;
        for t in &CARRY_TERMS[b[2]as usize..b[3]as usize]{let c=cache[100+t[0]as usize];v=if t[1]>0{v.add(c)}else{v.sub(c)};}
        let j=2*b[1]as usize+1;groups[j]=groups[j].add(high[b[0]as usize].mul(v));
    }
    let mut out=[K::ZERO;4];
    for block in 0usize..16{
        let values=core::array::from_fn(|lane|{
            let j=4*block+lane;let mut bits=j.trailing_ones()as usize;
            let mut v=if j+1<64{groups[2*(j+1)+1]}else{K::ZERO};
            while bits!=0{bits-=1;let r=j&!((1usize<<(bits+1))-1);v=v.add(groups[2*r+1]).half();}
            groups[2*j].add(v)
        });
        let h=core::array::from_fn(|lane|terminal_high[(4*block+lane)&15]);
        out[block/4]=out[block/4].add(qm31_sum_products4(values,h));
    }
    for v in &mut out{for _ in 0..8{*v=v.half();}}
    out
}
