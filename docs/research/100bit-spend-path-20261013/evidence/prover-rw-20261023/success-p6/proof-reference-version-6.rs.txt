//! Owned safe references only; never compiled into the shipped prover.
use aspis_core::field::{M31, CM31, QM31};
#[path = "../../../../crates/aspis-r1-cost-probe/src/ct_pole.rs"]
mod shipped_pole;

pub fn compress(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut out = QM31::from_cm31(CM31::from_m31(tag));
    let mut power = lambda;
    let mut i = 0usize;
    while i < values.len() {
        out = out.add(power.mul_m31(values[i]));
        power = power.mul(lambda);
        i += 1;
    }
    out
}

pub fn all_slots_clear(values: &[[[QM31;2];2]], masks: &[u16;64], chi: QM31) -> bool {
    let mut clear = true;
    let mut row = 0usize;
    while row < values.len() {
        let active = masks[row >> 4] & (1u16 << (row & 15)) != 0;
        clear = clear & !(active & shipped_pole::equal(chi, values[row][0][0]));
        clear = clear & !(active & shipped_pole::equal(chi, values[row][0][1]));
        clear = clear & !(active & shipped_pole::equal(chi, values[row][1][0]));
        clear = clear & !(active & shipped_pole::equal(chi, values[row][1][1]));
        row += 1;
    }
    clear
}

#[cfg(kani)]
mod checks {
    use super::*;
    fn q() -> QM31 {
        let x: [u32;4] = kani::any();
        QM31 { c0: CM31 { a:M31(x[0]), b:M31(x[1]) }, c1:CM31 { a:M31(x[2]), b:M31(x[3]) } }
    }
    fn raw(q:QM31) -> [u32;4] { [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0] }
    #[kani::proof]
    #[kani::unwind(18)]
    fn compression16() {
        let tag=M31(kani::any()); let lambda=q();
        let words: [u32;16]=kani::any();
        let mut values=[M31(0);16];
        let mut i=0;
        while i<16 {values[i]=M31(words[i]);i+=1;}
        let len:usize=kani::any(); kani::assume(len<=16);
        let before=words;
        let actual=aspis_statement::logup::compress_tagged_tuple(tag,&values[..len],lambda);
        let reference=compress(tag,&values[..len],lambda);
        assert_eq!(raw(actual),raw(reference));
        let mut j=0; while j<16 {assert_eq!(values[j].0,before[j]);j+=1;}
    }
    #[kani::proof]
    #[kani::unwind(3)]
    fn pole_row() {
        let row=[ [q(),q()], [q(),q()] ]; let chi=q();
        let mut masks=[0u16;64]; masks[0]=kani::any();
        let values=[row];
        assert_eq!(shipped_pole::all_slots_clear(&values,&masks,chi),all_slots_clear(&values,&masks,chi));
    }
}

pub fn wide_bytes(x: aspis_core::field::WideExact) -> [u8;32] { x.to_le_bytes() }

/// Indexed serialization reference retaining to_limbs and native LE conversion.
pub fn wide_bytes_reference(x: aspis_core::field::WideExact) -> [u8;32] {
    let limbs=x.to_limbs(); let mut out=[0u8;32];
    let mut i=0usize;
    while i<8 {
        out=write_limb(out,i,limbs[i]); i+=1;
    }
    out
}

#[cfg(kani)]
mod split_checks {
    use super::*;
    fn q() -> QM31 { let x:[u32;4]=kani::any(); QM31 {c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}} }
    fn raw(q:QM31) -> [u32;4] { [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0] }
    #[kani::proof]
    #[kani::unwind(18)]
    fn compression16_fixed() {
        let tag=M31(kani::any());let lambda=q();let words:[u32;16]=kani::any();
        let values=words.map(M31);
        let a=aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda);let b=compress(tag,&values,lambda);
        assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn wide_serialization() {
        let x=aspis_core::field::WideExact::new(q(),q());
        let actual=x.to_le_bytes(); let reference=wide_bytes_reference(x);
        let mut chunk=0; while chunk<8 { let mut byte=0; while byte<4 { assert_eq!(actual[4*chunk+byte],reference[4*chunk+byte]); byte+=1; } chunk+=1; }
    }
}

pub fn boundary_reference(p:&[QM31;28])->QM31 {
    let first=p[0];
    let mut a=2*u64::from(first.c0.a.0);let mut b=2*u64::from(first.c0.b.0);
    let mut c=2*u64::from(first.c1.a.0);let mut d=2*u64::from(first.c1.b.0);
    let mut i=1usize;
    while i<28 { (a,b,c,d)=sum_step(p[i],a,b,c,d); i+=1;}
    QM31{c0:CM31::new(M31::reduce_u64(a),M31::reduce_u64(b)),c1:CM31::new(M31::reduce_u64(c),M31::reduce_u64(d))}
}
#[cfg(kani)]
mod boundary_checks {
    use super::*;
    #[kani::proof]
    #[kani::unwind(30)]
    fn boundary28() {
        let raw:[[u32;4];28]=kani::any();let mut p=[QM31::ZERO;28];let mut i=0;
        while i<28 {let x=raw[i];p[i]=QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}};i+=1;}
        let a=aspis_core::state_only_sumcheck::state_only_boundary_sum(&p);let b=boundary_reference(&p);
        assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
    }
}

pub fn write_limb(mut out:[u8;32],i:usize,limb:u32)->[u8;32] {
 let bytes=limb.to_le_bytes();out[4*i]=bytes[0];out[4*i+1]=bytes[1];out[4*i+2]=bytes[2];out[4*i+3]=bytes[3];out
}
pub fn sum_step(x:QM31,a:u64,b:u64,c:u64,d:u64)->(u64,u64,u64,u64) {
 (a+u64::from(x.c0.a.0),b+u64::from(x.c0.b.0),c+u64::from(x.c1.a.0),d+u64::from(x.c1.b.0))
}

pub fn wide_bytes_flat(x:aspis_core::field::WideExact)->[u8;32] {
 let l=x.to_limbs();let a=l[0].to_le_bytes();let b=l[1].to_le_bytes();let c=l[2].to_le_bytes();let d=l[3].to_le_bytes();
 let e=l[4].to_le_bytes();let f=l[5].to_le_bytes();let g=l[6].to_le_bytes();let h=l[7].to_le_bytes();
 [a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]
}
#[cfg(kani)]
mod flat_checks {
 use super::*;
 #[kani::proof]
 #[kani::unwind(10)]
 fn wide_flat() {
  let raw:[u32;8]=kani::any();let q=|i:usize|QM31{c0:CM31{a:M31(raw[i]),b:M31(raw[i+1])},c1:CM31{a:M31(raw[i+2]),b:M31(raw[i+3])}};
  let x=aspis_core::field::WideExact::new(q(0),q(4));let a=x.to_le_bytes();let b=wide_bytes_flat(x);
  let mut i=0;while i<8 {let mut j=0;while j<4 {assert_eq!(a[4*i+j],b[4*i+j]);j+=1;}i+=1;}
 }
}

/// One owned accumulator avoids the backend's four-scalar loop join.
pub struct BoundaryAcc { pub a:u64, pub b:u64, pub c:u64, pub d:u64 }
pub fn boundary_acc_step(x:QM31,s:BoundaryAcc)->BoundaryAcc {
 BoundaryAcc { a:s.a+u64::from(x.c0.a.0), b:s.b+u64::from(x.c0.b.0), c:s.c+u64::from(x.c1.a.0), d:s.d+u64::from(x.c1.b.0) }
}
pub fn boundary_owned(p:&[QM31;28])->QM31 {
 let x=p[0];
 let mut s=BoundaryAcc {a:2*u64::from(x.c0.a.0),b:2*u64::from(x.c0.b.0),c:2*u64::from(x.c1.a.0),d:2*u64::from(x.c1.b.0)};
 let mut i=1usize;
 while i<28 { s=boundary_acc_step(p[i],s);i+=1; }
 QM31{c0:CM31::new(M31::reduce_u64(s.a),M31::reduce_u64(s.b)),c1:CM31::new(M31::reduce_u64(s.c),M31::reduce_u64(s.d))}
}
#[cfg(kani)]
mod owned_checks {
 use super::*;
 fn q()->QM31 {let x:[u32;4]=kani::any();QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
 fn raw(x:QM31)->[u32;4] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
 #[kani::proof]
 #[kani::unwind(30)]
 fn boundary_owned28() {
  let mut p=[QM31::ZERO;28];let mut i=0;while i<28 {p[i]=q();i+=1;}
  assert_eq!(raw(aspis_core::state_only_sumcheck::state_only_boundary_sum(&p)),raw(boundary_owned(&p)));
 }
 #[kani::proof]
 #[kani::unwind(3)]
 fn compression_one() {
  let tag=M31(kani::any());let x=M31(kani::any());let lambda=q();
  assert_eq!(raw(aspis_statement::logup::compress_tagged_tuple(tag,&[x],lambda)),raw(compress(tag,&[x],lambda)));
 }
}

/// Fixed 28-coefficient boundary, unrolled at the proof-reference source.
pub fn boundary_flat(p:&[QM31;28])->QM31 {
 let x=p[0];
 let s=BoundaryAcc{a:2*u64::from(x.c0.a.0),b:2*u64::from(x.c0.b.0),c:2*u64::from(x.c1.a.0),d:2*u64::from(x.c1.b.0)};
 let s=boundary_acc_step(p[1],s);
 let s=boundary_acc_step(p[2],s);
 let s=boundary_acc_step(p[3],s);
 let s=boundary_acc_step(p[4],s);
 let s=boundary_acc_step(p[5],s);
 let s=boundary_acc_step(p[6],s);
 let s=boundary_acc_step(p[7],s);
 let s=boundary_acc_step(p[8],s);
 let s=boundary_acc_step(p[9],s);
 let s=boundary_acc_step(p[10],s);
 let s=boundary_acc_step(p[11],s);
 let s=boundary_acc_step(p[12],s);
 let s=boundary_acc_step(p[13],s);
 let s=boundary_acc_step(p[14],s);
 let s=boundary_acc_step(p[15],s);
 let s=boundary_acc_step(p[16],s);
 let s=boundary_acc_step(p[17],s);
 let s=boundary_acc_step(p[18],s);
 let s=boundary_acc_step(p[19],s);
 let s=boundary_acc_step(p[20],s);
 let s=boundary_acc_step(p[21],s);
 let s=boundary_acc_step(p[22],s);
 let s=boundary_acc_step(p[23],s);
 let s=boundary_acc_step(p[24],s);
 let s=boundary_acc_step(p[25],s);
 let s=boundary_acc_step(p[26],s);
 let s=boundary_acc_step(p[27],s);
 QM31{c0:CM31::new(M31::reduce_u64(s.a),M31::reduce_u64(s.b)),c1:CM31::new(M31::reduce_u64(s.c),M31::reduce_u64(s.d))}
}
#[cfg(kani)]
mod flat_boundary_checks {
 use super::*;
 #[kani::proof]
 #[kani::unwind(30)]
 fn boundary_flat28() {
 let raw:[[u32;4];28]=kani::any();let mut p=[QM31::ZERO;28];let mut i=0;
 while i<28 {let x=raw[i];p[i]=QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}};i+=1;}
 let a=aspis_core::state_only_sumcheck::state_only_boundary_sum(&p);let b=boundary_flat(&p);
 assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
 }
}

#[cfg(kani)]
mod scalar_compression_checks {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn compression_one_a() {
 let tag=M31(kani::any());let x=M31(kani::any());let raw:[u32;4]=kani::any();
 let lambda=QM31{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};
 let a=aspis_statement::logup::compress_tagged_tuple(tag,&[x],lambda);let b=compress(tag,&[x],lambda);
 assert_eq!(a.c0.a.0,b.c0.a.0);
 }
}

// Raw-input release comparison. The command uses --no-overflow-checks because
// the pinned native release has overflow-checks=false; unwinding and memory
// checks remain enabled. Split observable coordinates to keep each SAT goal small.
#[cfg(kani)]
mod release_compression_checks {
 use super::*;
 fn inputs()->(M31,QM31,[M31;16],usize) {
 let t=M31(kani::any());let raw:[u32;4]=kani::any();
 let l=QM31{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};
 let words:[u32;16]=kani::any();let mut v=[M31(0);16];let mut i=0;while i<16 {v[i]=M31(words[i]);i+=1;}
 let n:usize=kani::any();kani::assume(n<=16);(t,l,v,n)
 }
 #[kani::proof]
 #[kani::unwind(18)]
 fn compression_release_a() {
 let(t,l,v,n)=inputs();let a=aspis_statement::logup::compress_tagged_tuple(t,&v[..n],l);let b=compress(t,&v[..n],l);
 assert_eq!(a.c0.a.0,b.c0.a.0);
 }
 #[kani::proof]
 #[kani::unwind(18)]
 fn compression_release_bcd() {
 let(t,l,v,n)=inputs();let a=aspis_statement::logup::compress_tagged_tuple(t,&v[..n],l);let b=compress(t,&v[..n],l);
 assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
 }
}
