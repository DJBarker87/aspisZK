//! Owned cfg(kani)-only references, copied without body changes from the retained P6 source.
use aspis_core::field::{QM31,CM31,M31};
pub fn wide_bytes_flat(x:aspis_core::field::WideExact)->[u8;32] {
 let l=x.to_limbs();let a=l[0].to_le_bytes();let b=l[1].to_le_bytes();let c=l[2].to_le_bytes();let d=l[3].to_le_bytes();
 let e=l[4].to_le_bytes();let f=l[5].to_le_bytes();let g=l[6].to_le_bytes();let h=l[7].to_le_bytes();
 [a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]
}
pub struct BoundaryAcc { pub a:u64, pub b:u64, pub c:u64, pub d:u64 }
pub fn boundary_acc_step(x:QM31,s:BoundaryAcc)->BoundaryAcc {
 BoundaryAcc { a:s.a+u64::from(x.c0.a.0), b:s.b+u64::from(x.c0.b.0), c:s.c+u64::from(x.c1.a.0), d:s.d+u64::from(x.c1.b.0) }
}
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

pub fn helper_sum(h1:&[QM31])->Option<QM31> {
 if h1.len()!=1024 {return None;}
 let mut sum=QM31::ZERO;let mut index=0usize;
 while index<1024 {sum=sum.add(h1[index]);index+=1;}
 Some(sum)
}
