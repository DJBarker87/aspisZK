//! UNPROVED COST PROBE. Seven coefficient functionals and their dual folds.
use alloc::{boxed::Box,vec::Vec};
use aspis_core::{field::{QM31 as K,WideExact as E,M31},circle::SecureCirclePoint};
use crate::{transport::{Variant,TAU},verifier::Error};
pub const QUARTER:M31=M31(536870912);
pub const PERM:[usize;4]=[0,3,2,1];
pub fn powers<const N:usize>(x:E)->[E;N] { let mut p=E::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
pub fn kpowers<const N:usize>(x:K)->[K;N] { let mut p=K::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
pub fn double(x:K)->K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }

// Exact S2 coefficient-to-row inactive classification, in first-occurrence order.
// Exhaustive table correspondence is checked against Variant::row and raw(0, _).
const S2_INACTIVE_GROUPS:[u8;64]=[0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7];
const S2_INACTIVE_MASKS:[u16;12]=[32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024];

#[inline(never)]
fn s2_grouped_inactive_pair(f:&[u8],low:&[E;16])->E {
    let mut coefficients=[E::ZERO;12];
    for j in 0..64 {
        let group=S2_INACTIVE_GROUPS[j] as usize;
        coefficients[group]=coefficients[group].add(field(f,j));
    }
    let mut pair=E::ZERO;
    for group in 0..12 {
        let mut weight=E::ZERO;
        for (bit,&challenge) in low.iter().enumerate() {
            if S2_INACTIVE_MASKS[group]&(1<<bit)!=0 {weight=weight.add(challenge);}
        }
        pair=pair.add(coefficients[group].mul(weight));
    }
    pair
}

/// Contract the inactive row after combining coefficients with the same
/// sixteen-entry inactive mask. The zero mask is retained as a group; its
/// subset weight is zero, matching the ungrouped sum.
#[inline(never)]
fn grouped_inactive_pair(weights:&Weights,f:&[u8],low:&[E;16])->E {
    if weights.variant==Variant::S2 && f.len()==64*32 {return s2_grouped_inactive_pair(f,low);}
    let mut group_masks=[0u16;64];
    let mut group_coefficients=[E::ZERO;64];
    let mut groups=0;
    for j in 0..f.len()/32 {
        let mut mask=0u16;
        for s in 0..16 {if weights.raw(0,16*j+s)==K::ONE {mask|=1<<s;}}
        let coefficient=field(f,j);
        let mut group=0;
        while group<groups && group_masks[group]!=mask {group+=1;}
        if group==groups {group_masks[group]=mask;groups+=1;}
        group_coefficients[group]=group_coefficients[group].add(coefficient);
    }
    let mut pair=E::ZERO;
    for group in 0..groups {
        let mask=group_masks[group];
        let mut weight=E::ZERO;
        for (s,&challenge) in low.iter().enumerate() {
            if mask&(1<<s)!=0 {weight=weight.add(challenge);}
        }
        pair=pair.add(group_coefficients[group].mul(weight));
    }
    pair
}

/// Build the four two-fold Libra dual weights without per-cell exponentiation.
#[inline(never)]
fn twofold_libra_weights(low:&[E;16],extra:[K;2])->[E;4] {
    let powers:[[K;28];2]=core::array::from_fn(|side| {
        let mut power=K::ONE;
        core::array::from_fn(|_| {let value=power;power=power.mul(extra[side]);value})
    });
    core::array::from_fn(|j| {
        let mut weight=E::ZERO;
        for s in 0..16 {
            let index=16*j+s;
            if index<56 {
                weight=weight.add(low[s].mul_qm31(powers[index/28][index%28]));
            }
        }
        weight
    })
}

pub struct Weights {
    pub variant:Variant,
    pub factors:[[[K;4];5];5],
    pub points:[[K;10];3],
    pub extra:[K;2],
}
impl Weights {
    #[inline(never)]
    pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Box<Self>,Error> {
        let mut out=aspis_core::r0::heap::uninit::<Self>().map_err(|_|Error::Allocation)?;
        unsafe {
            let p=out.as_mut_ptr();
            core::ptr::addr_of_mut!((*p).variant).write(variant);
            core::ptr::addr_of_mut!((*p).points).write(aspis_core::state_only_prefix::r0::statement_points(alpha));
            core::ptr::addr_of_mut!((*p).extra).write([alpha[8],alpha[9]]);
            for k in 0..3 { for d in 0..5 {
                let a=(*p).points[k][9-2*TAU[d]]; let b=(*p).points[k][8-2*TAU[d]];
                (*p).factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
            }}
            for k in 0..2 {
                (*p).factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];
                let mut x=double(z[k].x);
                for d in 1..5 {
                    let y=double(x); (*p).factors[3+k][d]=[K::ONE,x,y,x.mul(y)]; x=double(y);
                }
            }
            Ok(out.assume_init())
        }
    }
    pub fn raw(&self,kind:usize,j:usize)->K {
        match kind {
            0=>if aspis_core::r0::opening::inactive(self.variant.row(j)).unwrap() {K::ONE} else {K::ZERO},
            4=>if j<56 { self.extra[j/28].pow((j%28) as u64) } else {K::ZERO},
            1..=3 if self.variant==Variant::D => {
                let r=self.variant.row(j);
                (0..10).fold(K::ONE,|v,b|v.mul(if r&(1<<b)==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]}))
            },
            _=> {
                let k=if kind<4 {kind-1}else{kind-2};
                (0..5).fold(K::ONE,|v,d|v.mul(self.factors[k][d][(j>>(2*d))&3]))
            }
        }
    }
    fn scalar_factor(f:&[K;4],p:&[E;4])->E {
        (0..4).fold(E::ZERO,|v,s|v.add(p[PERM[s]].mul_qm31(f[s]))).mul_m31(QUARTER)
    }
    fn tensor(&self,k:usize,folds:usize,output:&mut[K]) {
        output[0]=K::ONE;let mut n=1;
        for d in folds..5 {
            for j in (0..n).rev() {
                let x=output[j];
                for s in 0..4 { output[j+s*n]=x.mul(self.factors[k][d][s]); }
            }
            n*=4;
        }
    }
    pub fn dual_raw(&self,kind:usize,j:usize,alpha:&[E])->E {
        let p0=powers::<4>(alpha[0]);
        let p1=if alpha.len()==2 {powers::<4>(alpha[1])}else{[E::ONE;4]};
        let width=1<<(2*alpha.len());
        let mut sum=E::ZERO;
        for s in 0..width {
            let p=p0[PERM[s%4]].mul(p1[PERM[s/4]]);
            sum=sum.add(p.mul_qm31(self.raw(kind,width*j+s)));
        }
        for _ in alpha { sum=sum.mul_m31(QUARTER); }
        sum
    }
    /// Product rows keep a K tensor after their low digits have been folded.
    /// Only the contracted scalar is in E. Sparse rows are handled separately.
    #[inline(never)]
    pub fn pair(&self,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error> {
        let n=f.len()/32; let folds=alpha.len();
        if n!=1024>>(2*folds) {return Err(Error::Parse);}
        let ap0=powers::<4>(alpha[0]);
        let ap1=if folds==2 {powers::<4>(alpha[1])}else{[E::ONE;4]};
        let mut scratch=aspis_core::r0::heap::filled(n,K::ZERO).map_err(|_|Error::Allocation)?;
        let mut parts=[E::ZERO;7];
        // On S2's two-fold path the high tensor factors for point rows 0 and
        // 2 are identical. Keep the equality guard so arbitrary constructed
        // `Weights` values retain the original per-row fallback.
        let shared_two_point = self.variant==Variant::S2 && folds==2
            && self.factors[0][2]==self.factors[2][2]
            && self.factors[0][3]==self.factors[2][3];
        for kind in [1usize,2,3,5,6] {
            if shared_two_point && (kind==1 || kind==3) { continue; }
            if self.variant==Variant::D && kind<4 {
                parts[kind]=self.dense_point_pair(kind,alpha,f)?;
            } else {
                let k=if kind<4 {kind-1}else{kind-2};
                self.tensor(k,folds,&mut scratch);
                let mut scale=Self::scalar_factor(&self.factors[k][0],&ap0);
                if folds==2 {scale=scale.mul(Self::scalar_factor(&self.factors[k][1],&ap1));}
                let mut pair=crate::fast_pairing::EbyKDot::new();
                for j in 0..n {pair.push(field(f,j),scratch[j]).map_err(|_|Error::Parse)?;}
                parts[kind]=scale.mul(pair.finish());
            }
        }
        if shared_two_point {
            // The two point rows share the d2/d3 coefficients. Preserve the
            // tensor's least-significant-first order: d2 is j mod 4 and d3
            // is j / 4. Each d4 slice then contracts one 16-term EbyKDot.
            let common:[K;16]=core::array::from_fn(|j|
                self.factors[0][2][j&3].mul(self.factors[0][3][j>>2]));
            let mut partials=[E::ZERO;4];
            for s in 0..4 {
                let mut dot=crate::fast_pairing::EbyKDot::new();
                for j in 0..16 {
                    dot.push(field(f,16*s+j),common[j]).map_err(|_|Error::Parse)?;
                }
                partials[s]=dot.finish();
            }
            for (kind,k) in [(1usize,0usize),(3usize,2usize)] {
                let mut high=crate::fast_pairing::EbyKDot::new();
                for s in 0..4 {
                    high.push(partials[s],self.factors[k][4][s]).map_err(|_|Error::Parse)?;
                }
                let scale=Self::scalar_factor(&self.factors[k][0],&ap0)
                    .mul(Self::scalar_factor(&self.factors[k][1],&ap1));
                parts[kind]=scale.mul(high.finish());
            }
        }
        if folds==1 {
            let dual:[E;16]=core::array::from_fn(|mask|(0..4).filter(|&s|mask&(1<<s)!=0).fold(E::ZERO,|v,s|v.add(ap0[PERM[s]])).mul_m31(QUARTER));
            let mut groups=[E::ZERO;16];
            for j in 0..n {
                let mut mask=0;
                for s in 0..4 {if self.raw(0,4*j+s)==K::ONE {mask|=1<<s;}}
                groups[mask]=groups[mask].add(field(f,j));
            }
            for m in 1..16 {parts[0]=parts[0].add(groups[m].mul(dual[m]));}
            for side in 0..2 {
                let p=kpowers::<5>(self.extra[side]);
                let scale=Self::scalar_factor(&[p[0],p[1],p[2],p[3]],&ap0);
                let mut power=K::ONE; let mut pair=E::ZERO;
                for j in 0..7 {pair=pair.add(field(f,j+7*side).mul_qm31(power));power=power.mul(p[4]);}
                parts[4]=parts[4].add(pair.mul(scale));
            }
        } else {
            // Two-fold 0/1 row: compute the sixteen challenge products once.
            // Coefficients with the same inactive mask share one subset sum.
            let low:[E;16]=core::array::from_fn(|s|ap0[PERM[s%4]].mul(ap1[PERM[s/4]]).mul_m31(QUARTER.mul(QUARTER)));
            parts[0]=grouped_inactive_pair(self,f,&low);
            let libra=twofold_libra_weights(&low,self.extra);
            for j in 0..4 {parts[4]=parts[4].add(field(f,j).mul(libra[j]));}
        }
        #[cfg(feature="prover")]
        for kind in 0..7 {
            for j in 0..1024 {crate::trace::value(6,kind*1024+j,E::from_qm31(self.raw(kind,j)));}
            for j in 0..n {crate::trace::value(7,kind*n+j,self.dual_raw(kind,j,alpha));}
        }
        let k=powers::<7>(kappa);let mut sum=E::ZERO;
        for kind in 0..7 {crate::trace::value(8,kind,parts[kind]);sum=sum.add(k[kind].mul(parts[kind]));}
        Ok(sum)
    }
    #[inline(never)]
    fn dense_point_pair(&self,kind:usize,alpha:&[E],f:&[u8])->Result<E,Error> {
        // D keeps the full eq tensor. Hoist the sixteen shared E products
        // before combining its K entries; no tensor factorization is assumed.
        let mut rows=aspis_core::r0::heap::filled(1024,K::ZERO).map_err(|_|Error::Allocation)?;
        rows[0]=K::ONE;let mut width=1;
        for b in 0..10 {
            let p=self.points[kind-1][9-b];
            for j in (0..width).rev() {let x=rows[j];rows[j+width]=x.mul(p);rows[j]=x.mul(K::ONE.sub(p));}
            width*=2;
        }
        let a=powers::<4>(alpha[0]);let b=powers::<4>(alpha[1]);
        let low:[E;16]=core::array::from_fn(|s|a[PERM[s%4]].mul(b[PERM[s/4]]).mul_m31(QUARTER.mul(QUARTER)));
        let mut pair=E::ZERO;
        for j in 0..64 {
            let mut w=E::ZERO;
            for s in 0..16 {w=w.add(low[s].mul_qm31(rows[self.variant.row(16*j+s)]));}
            pair=pair.add(field(f,j).mul(w));
        }
        Ok(pair)
    }
    pub fn materialize(&self,kappa:E)->Result<Vec<E>,Error> {
        let kp=powers::<7>(kappa);
        let mut w=aspis_core::r0::heap::filled(1024,E::ZERO).map_err(|_|Error::Allocation)?;
        for (j,v) in w.iter_mut().enumerate() {for kind in 0..7 {*v=v.add(kp[kind].mul_qm31(self.raw(kind,j)));}}
        Ok(w)
    }
}

#[cfg(test)]
mod s2_inactive_table_tests {
    use super::*;
    #[test]
    fn all_s2_inactive_table_entries_match_reference() {
        for j in 0..64 {
            let group=S2_INACTIVE_GROUPS[j] as usize;
            assert!(group<S2_INACTIVE_MASKS.len());
            for bit in 0..16 {
                assert_eq!((S2_INACTIVE_MASKS[group]>>bit)&1!=0,
                    aspis_core::r0::opening::inactive(Variant::S2.row(16*j+bit)).unwrap());
            }
        }
        // Equality of each coefficient's scalar factor establishes the
        // regrouping identity independently of particular message values.
        for bit in 0..16 {
            let low=core::array::from_fn(|i|if i==bit {E::ONE}else{E::ZERO});
            for j in 0..64 {
                let mut f=alloc::vec![0u8;64*32];f[j*32..(j+1)*32].copy_from_slice(&E::ONE.to_le_bytes());
                let expected=if aspis_core::r0::opening::inactive(Variant::S2.row(16*j+bit)).unwrap(){E::ONE}else{E::ZERO};
                assert_eq!(s2_grouped_inactive_pair(&f,&low),expected);
            }
        }
    }
}
