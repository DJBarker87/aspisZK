//! Weighted extension of the retained grouped contraction. Research only.
//! Public support lengths control work; coefficient values never select paths.
use super::{corelib,K,M31};
include!("r17_reused_group_geometry.rs");

pub(super) struct Kernel { normal:[K;16],carry:[K;3],high:[K;16] }
impl Kernel {
    pub(super) fn new(abc:[K;3],alpha:[K;4])->Self {
        let (normal,carry,high)=geometry(abc,alpha);
        Self{normal,carry,high}
    }
    fn contract(&self,read:impl Fn(usize)->(K,K))->[K;4] {
        let mut out=[K::ZERO;4];
        // Do NOT restrict j to the input support: active carries can reach
        // high terminal groups even when all ordinary weights there are zero.
        for j in 0..64 {
            let mut value=read(j).0;
            for (r,s) in edges(j) {
                if r<64 {value=value.add(read(r).1.mul_m31(s));}
            }
            out[j>>4]=out[j>>4].add(value.mul(self.high[j&15]));
        }
        for value in &mut out {for _ in 0..8 {*value=value.half();}}
        out
    }
    pub(super) fn prefix(&self,values:&[K])->[K;4] {
        assert!(values.len()<=1024);
        let sums:Vec<(K,K)>=values.chunks(16).map(|row| {
            let normal=row.iter().enumerate().fold(K::ZERO,|s,(j,&v)|s.add(v.mul(self.normal[j])));
            let carry=row.iter().take(3).enumerate().fold(K::ZERO,|s,(j,&v)|s.add(v.mul(self.carry[j])));
            (normal,carry)
        }).collect();
        self.contract(|j|sums.get(j).copied().unwrap_or((K::ZERO,K::ZERO)))
    }
    pub(super) fn binary_masks(&self,masks:&[u16;64])->[K;4] {
        // Binary fixed coefficients need additions, not general multipliers.
        let sums:Vec<(K,K)>=masks.iter().map(|&mask| {
            let mut normal=K::ZERO;let mut carry=K::ZERO;
            for j in 0..16 {if mask&(1<<j)!=0 {
                normal=normal.add(self.normal[j]);
                if j<3 {carry=carry.add(self.carry[j]);}
            }}
            (normal,carry)
        }).collect();
        self.contract(|j|sums[j])
    }
    pub(super) fn coordinate(&self,row:usize)->[K;4] {
        assert!(row<1024);
        self.contract(|j|if j==row/16 {
            (self.normal[row%16],if row%16<3 {self.carry[row%16]}else{K::ZERO})
        } else {(K::ZERO,K::ZERO)})
    }
}
