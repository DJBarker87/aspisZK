//! Executable mirror of ResidualModel.lean versus the pinned source.
//! Public prefixes remain unchanged; no privacy conclusion from these checks.
extern crate aspis_core as corelib;
use corelib::field::{M31,M31_HALF,M31_QUARTER,QM31 as K};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension};
#[path="r16_basis_transport.rs"] mod basis_transport;
#[path="r17_structured_g.rs"] mod structured_g;
mod r18_sparse_coded_g;mod r17_mask_workspace;mod r17_tensor_prefix;
#[path="r17_opening_weights.rs"] mod opening_weights;
mod r28_source_helpers;
mod fixed {include!("r17_basis_tables.rs");}
use r28_source_helpers::{chord,dot,times_x};
fn xentry(j:usize,r:usize)->K{let(mut row,mut bit)=(j,0);let mut sum=K::ZERO;while row&(1<<bit)!=0{row^=1<<bit;bit+=1;if row==r{sum=sum.add(K::ONE.mul_m31(M31_HALF).pow(bit as u64));}}if row|(1<<bit)==r{sum=sum.add(K::ONE.mul_m31(M31_HALF).pow(bit as u64));}sum}
fn xxentry(j:usize,r:usize)->K{(0..j+2).fold(K::ZERO,|s,i|s.add(xentry(j,i).mul(xentry(i,r))))}
fn delta(j:usize,r:usize)->K{if j==r{K::ONE}else{K::ZERO}}
fn centry(j:usize,r:usize,[a,b,c]:[K;3])->K{let d=delta(j/2,r/2);if j%2==0{if r%2==0{a.mul(d).add(b.mul(xentry(j/2,r/2)))}else{c.mul(d)}}else if r%2==0{c.mul(d.sub(xxentry(j/2,r/2)))}else{a.mul(d).add(b.mul(xentry(j/2,r/2)))}}
fn point(z:&[K;10],which:usize)->[K;10]{std::array::from_fn(|i|if which==0{z[i]}else if which==1{let carry=(i+1..10).fold(K::ONE,|s,j|s.mul(z[j]));z[i].add(carry).sub(z[i].mul(carry).add(z[i].mul(carry)))}else if i==6||i==7{K::ONE.sub(z[i])}else{z[i]})}
fn tensor(z:&[K;10],r:usize)->K{(0..10).fold(K::ONE,|s,i|s.mul(if (r>>(9-i))&1==0{K::ONE.sub(z[i])}else{z[i]}))}
fn shifted(p:&[K],n:usize)->[K;27]{let mut v=[K::ZERO;27];v[..23].copy_from_slice(p);for _ in 0..n{v=std::array::from_fn(|r|(0..27).fold(K::ZERO,|s,j|s.add(v[j].mul(xentry(j,r)))));}v}
fn quotient(p:&[K],col:usize,alpha:K)->[K;108]{let v=shifted(p,col/3);let slot=col%3+1;std::array::from_fn(|r|if r%4==0{alpha.pow(slot as u64).mul(v[r/4]).neg()}else if r%4==slot{v[r/4]}else{K::ZERO})}
fn poly(q:&[K;108],w:&[K;108],reverse:bool)->[K;7]{let mut out=[K::ZERO;7];for block in 0..27{for a in 0..4{for b in 0..4{let slot=if reverse{(4-b)%4}else{b};out[a+b]=out[a+b].add(q[4*block+a].mul(w[4*block+slot]).mul_m31(M31_QUARTER));}}}out}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);let bytes=std::fs::read(&args[1]).unwrap();assert_eq!(bytes.len(),424);
    let f:Vec<_>=bytes[..336].chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();let z:[K;10]=f[..10].try_into().unwrap();let(k,tau,alpha)=(f[10],f[11],f[12]);let(sx,sy,zx,zy)=(f[13],f[14],f[15],f[16]);let abc=[sx.mul(zy).sub(sy.mul(zx)),sy.sub(zy),zx.sub(sx)];
    let queries:Vec<_>=bytes[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();let map=basis_transport::transport();
    assert_eq!(map.order.as_slice(),&fixed::ORDER);assert_eq!(map.inactive.as_slice(),&fixed::INACTIVE);assert!(fixed::ORDER[..111].iter().all(|&r|r!=1023));
    for j in 0..27{let mut unit=vec![K::ZERO;27];unit[j]=K::ONE;let x=times_x(&unit);for r in 0..28{assert_eq!(x[r],xentry(j,r));}}
    let mut cm=vec![[K::ZERO;111];108];for r in 0..108{let mut unit=vec![K::ZERO;1024];unit[r]=K::ONE;let c=chord(&unit,abc);assert!(c[111..].iter().all(|&v|v==K::ZERO));for j in 0..111{cm[r][j]=centry(r,j,abc);assert_eq!(cm[r][j],c[j]);}}
    let source_points=corelib::v6_transcript::v6_statement_points(&z);let mut ew=vec![[K::ZERO;108];3];let mut source_point_weights=Vec::new();let mut pivot_negative=0;
    for which in 0..3{let z1=point(&z,which);assert_eq!(z1,source_points[which]);let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,source_points[which].to_vec()).unwrap();let dense:Vec<_>=(0..1024).map(|i|w.weight_at(i)).collect();for r in 0..1024{assert_eq!(tensor(&z1,r),dense[r]);}
        let code:[K;111]=std::array::from_fn(|j|{let r=fixed::ORDER[j];tensor(&z1,r).sub(if fixed::INACTIVE[r]{tensor(&z1,1023)}else{K::ZERO})});let transported=opening_weights::chord_transpose(&map.dual(&dense),abc);
        for r in 0..108{ew[which][r]=(0..111).fold(K::ZERO,|s,j|s.add(code[j].mul(cm[r][j])));assert_eq!(ew[which][r],transported[r]);let bad=(0..111).fold(K::ZERO,|s,j|s.add(tensor(&z1,fixed::ORDER[j]).mul(cm[r][j])));if bad!=ew[which][r]{pivot_negative+=1;}}
        source_point_weights.push(dense);
    }assert!(pivot_negative>0);
    assert!((0..9).any(|i|source_points[1][i]!=K::ONE.sub(z[i])));let mut reversed=z;reversed.reverse();assert!((0..1024).any(|r|tensor(&z,r)!=tensor(&reversed,r)));
    let mut p=vec![K::ONE];for pt in corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap(){let root=pt.x.mul(pt.x).double().sub(M31::ONE);let mut n=times_x(&p);for j in 0..p.len(){n[j]=n[j].sub(p[j].mul_m31(root));}p=n;}
    let rw=opening_weights::quotient_weights(&z,k,abc,tau,false);let gw=opening_weights::quotient_weights(&z,k,abc,tau,true);
    let mr:[K;108]=std::array::from_fn(|r|k.mul(ew[0][r]).add(k.pow(2).mul(ew[1][r])).add(k.pow(3).mul(ew[2][r])));let mg:[K;108]=std::array::from_fn(|r|k.pow(2).mul(ew[1][r]).add(k.pow(3).mul(ew[2][r])));
    for r in 0..108{assert_eq!(mr[r],rw.weight_at(r as u32));assert_eq!(mg[r],gw.weight_at(r as u32));}
    let mut polyslot_negative=0;let mut minor=vec![vec![K::ZERO;13];13];let rows=[1,2,3,4,5,6,7,8,10,11,12,13,15];
    let mut source_v=p.clone();
    for col in 0..13{if col>0&&col%3==0{source_v=times_x(&source_v);}let q=quotient(&p,col,alpha);let mut full=vec![K::ZERO;1024];let slot=col%3+1;for(j,&v)in source_v.iter().enumerate(){full[4*j+slot]=v;full[4*j]=alpha.pow(slot as u64).mul(v).neg();}assert_eq!(q.as_slice(),&full[..108]);assert!(full[108..].iter().all(|&v|v==K::ZERO));
        let m=map.inverse(&chord(&full,abc));assert!(structured_g::mixed_coins(&m).iter().all(|&v|v==K::ZERO));let mut o=vec![K::ZERO,dot(&q,&ew[1]),dot(&q,&ew[2])];let pr=poly(&q,&mr,true);let pg=poly(&q,&mg,true);o.extend(pr);o.extend(pg);
        for i in 1..3{assert_eq!(o[i],dot(&source_point_weights[i],&m));}assert_eq!(pr,polynomial_for_extension(&full,&rw));assert_eq!(pg,polynomial_for_extension(&full,&gw));if poly(&q,&mr,false)!=pr{polyslot_negative+=1;}for(i,&r)in rows.iter().enumerate(){minor[i][col]=o[r];}
    }assert!(polyslot_negative>0);
    let out=std::path::Path::new(&args[2]);assert!(!out.exists());std::fs::create_dir(out).unwrap();let mut mb=Vec::new();for row in minor{for v in row{let mut b=[0;16];v.write_le_bytes(&mut b);mb.extend(b);}}std::fs::write(out.join("model-minor.bin"),mb).unwrap();
    let order=fixed::ORDER[..111].iter().map(|r|r.to_string()).collect::<Vec<_>>().join(",");let inactive=fixed::ORDER[..111].iter().map(|&r|fixed::INACTIVE[r].to_string()).collect::<Vec<_>>().join(",");
    std::fs::write(out.join("ResidualPins.lean"),format!("/- Generated from the source-pinned T163 table, verified against the source constructor. -/\nimport AspisV8R19.ResidualModel\nnamespace AspisR19.ResidualPins\ndef order : Fin 111 → Nat := fun i => [{order}].getD i.val 0\ndef inactive : Fin 111 → Bool := fun i => [{inactive}].getD i.val false\ntheorem order_bounds : ∀ i, order i<1023 := by decide\n#print axioms order_bounds\nend AspisR19.ResidualPins\n")).unwrap();
    std::fs::write(out.join("summary.json"),format!("{{\"source_prefixes\":1,\"table_checks\":2048,\"xentry_checks\":756,\"chord_entry_checks\":11988,\"chord_tail_checks\":108,\"point_checks\":30,\"tensor_checks\":3072,\"transported_point_checks\":324,\"low_weight_checks\":216,\"quotient_checks\":1404,\"residual_checks\":208,\"pivot_negative_entries\":{pivot_negative},\"slot_negative_columns\":{polyslot_negative},\"negative_families\":4,\"full_privacy\":false,\"source_prefix_substituted\":false}}\n")).unwrap();
    println!("R36_RESIDUAL_MODEL chord_entries=11988 tensor=3072 point_weights=324 residual_entries=208 negative_families=4 full_privacy=false");
}
