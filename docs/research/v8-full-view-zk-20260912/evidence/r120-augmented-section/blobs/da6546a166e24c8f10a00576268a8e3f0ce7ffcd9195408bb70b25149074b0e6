//! Rebind the old high-coordinate residual strategy to the actual two-swap map.
//! Fixed algebraic probes only: neither accepted prefixes nor a privacy theorem.
extern crate aspis_core as corelib;
use corelib::field::{QM31 as K,M31};
use corelib::sumcheck::{WeightAccumulator,polynomial_for_extension};
#[path="r16_basis_transport.rs"]mod basis_transport;
#[path="r17_structured_g.rs"]mod structured_g;
#[path="r17_opening_weights.rs"]mod opening_weights;
mod r18_sparse_coded_g;mod r17_mask_workspace;mod r17_tensor_prefix;
include!("r118_primal_source.rs");
use r17_coupled_audit::{dot,chord,times_x};
fn b(v:u32)->K{K::ONE.mul_m31(M31(v))}
fn residue(v:K)->u32{let mut bytes=[0;16];v.write_le_bytes(&mut bytes);assert_eq!(&bytes[4..],&[0;12]);u32::from_le_bytes(bytes[..4].try_into().unwrap())}
fn pivots(mut a:Vec<Vec<K>>)->Vec<usize>{
    let mut pivots=vec![];
    for c in 0..a[0].len(){let r=pivots.len();let Some(p)=(r..a.len()).find(|&i|a[i][c]!=K::ZERO)else{continue};
        a.swap(r,p);let inv=a[r][c].inv();for j in c..a[0].len(){a[r][j]=a[r][j].mul(inv);}
        for i in 0..a.len(){if i==r{continue;}let f=a[i][c];for j in c..a[0].len(){a[i][j]=a[i][j].sub(f.mul(a[r][j]));}}
        pivots.push(c);if pivots.len()==a.len(){break;}
    }pivots
}
fn make_q(v:&[K],slot:usize)->Vec<K>{
    let mut q=vec![K::ZERO;1024];
    for(j,&v)in v.iter().enumerate(){q[4*j+slot]=v;q[4*j]=b(7).pow(slot as u64).mul(v).neg();}
    q
}
fn main(){
    let path=std::env::args().nth(1).unwrap();let out=std::path::Path::new(&path);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let map=basis_transport::transport();assert_eq!([map.order[126],map.order[127],map.order[1021],map.order[1023]],[993,1009,1022,1023]);
    let cases=[
      ("old_T163_specialization",[0,0,0,1,1,0,0,1,0,2]),
      ("high_code_support_pivot_check",[1,1,2,3,4,0,2,3,4,2]),
      ("high_code_support_two_zero_carries",[1,1,2,3,4,0,2,3,0,2])];
    let rows=[1usize,2,3,4,5,6,7,8,10,11,12,13,15];
    let columns:Vec<usize>=(0..27).chain([29]).collect();let abc=[b(7),b(5),b(5).neg()];
    let mut results=vec![];
    for(name,zraw)in cases{
        let z=zraw.map(b);let points=corelib::v6_transcript::v6_statement_points(&z);
        let weights:Vec<Vec<K>>=points.iter().map(|p|{let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,p.to_vec()).unwrap();(0..1024).map(|i|w.weight_at(i)).collect()}).collect();
        let ew:Vec<_>=weights.iter().map(|w|opening_weights::chord_transpose(&map.dual(w),abc)).collect();
        let low_nonzero:Vec<_>=ew.iter().map(|w|w[..88].iter().filter(|&&x|x!=K::ZERO).count()).collect();
        let rw=opening_weights::quotient_weights(&z,b(5),abc,b(17),false);
        let gw=opening_weights::quotient_weights(&z,b(5),abc,b(17),true);
        let channel_low=[&rw,&gw].map(|w|(0..88).filter(|&i|w.weight_at(i)!=K::ZERO).count());
        let observe=|q:&Vec<K>|{
            let code=chord(q,abc);assert!(code[131..].iter().all(|&x|x==K::ZERO));assert_eq!(code[128],K::ZERO);
            let original=map.inverse(&code);assert!(structured_g::mixed_coins(&original).iter().all(|&x|x==K::ZERO));
            assert_eq!(map.forward(&original),code);
            for v in q.chunks_exact(4){assert_eq!(v[0].add(b(7).mul(v[1].add(b(7).mul(v[2].add(b(7).mul(v[3])))))),K::ZERO);}
            let mut obs:Vec<_>=weights.iter().map(|w|dot(&original,w)).collect();
            obs.extend(polynomial_for_extension(q,&rw));obs.extend(polynomial_for_extension(q,&gw));obs
        };
        let os:Vec<_>=columns.iter().map(|&c|{let mut v=vec![K::ZERO;32];v[22+c/3]=K::ONE;observe(&make_q(&v,c%3+1))}).collect();
        let full:Vec<Vec<K>>=(0..17).map(|r|os.iter().map(|o|o[r]).collect()).collect();
        let selected:Vec<Vec<K>>=rows.iter().map(|&r|full[r].clone()).collect();
        let piv=pivots(selected.clone());let full_rank=pivots(full).len();
        let root_independent_precondition=low_nonzero==[0,0,0]&&channel_low==[0,0];
        let mut normalized_checks=0;
        if root_independent_precondition{
            // The same section strategy: root corrections occupy only q[0..88].
            // This checks four source-derived root families, not all tuples.
            for queries in [(0..22).collect::<Vec<u32>>(),(0..22).map(|i|2*i).collect(),(0..11).flat_map(|i|[2*i*997,2*i*997+1]).collect(),(0..20).chain([1000,1001]).collect()]{
                let mut p=vec![K::ONE];
                for pt in corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap(){
                    let root=pt.x.mul(pt.x).double().sub(M31::ONE);let mut next=times_x(&p);
                    for i in 0..p.len(){next[i]=next[i].sub(p[i].mul_m31(root));}p=next;
                }
                let mut shifts=vec![p];for i in 1..10{shifts.push(times_x(&shifts[i-1]));}
                for(at,&c)in columns.iter().enumerate(){
                    let d=22+c/3;let mut rem=vec![K::ZERO;32];rem[d]=K::ONE;
                    for top in (22..=d).rev(){let f=rem[top].mul(shifts[top-22][top].inv());for j in 0..=top{rem[j]=rem[j].sub(f.mul(shifts[top-22][j]));}}
                    assert!(rem[22..].iter().all(|&x|x==K::ZERO));let mut v:Vec<_>=rem.iter().map(|x|x.neg()).collect();v[d]=K::ONE;
                    assert_eq!(observe(&make_q(&v,c%3+1)),os[at]);normalized_checks+=17;
                }
            }
        }
        let mut determinant=None;
        if piv.len()==13{
            let mut a:Vec<Vec<K>>=selected.iter().map(|r|piv.iter().map(|&c|r[c]).collect()).collect();let matrix=a.clone();
            let mut inverse=vec![vec![K::ZERO;13];13];for i in 0..13{inverse[i][i]=K::ONE;}let mut det=K::ONE;
            for c in 0..13{
                let p=(c..13).find(|&r|a[r][c]!=K::ZERO).unwrap();if p!=c{a.swap(c,p);inverse.swap(c,p);det=det.neg();}
                det=det.mul(a[c][c]);let inv=a[c][c].inv();for j in 0..13{a[c][j]=a[c][j].mul(inv);inverse[c][j]=inverse[c][j].mul(inv);}
                for r in 0..13{if r==c{continue;}let f=a[r][c];for j in 0..13{a[r][j]=a[r][j].sub(f.mul(a[c][j]));inverse[r][j]=inverse[r][j].sub(f.mul(inverse[c][j]));}}
            }
            for i in 0..13{for j in 0..13{assert_eq!((0..13).fold(K::ZERO,|s,k|s.add(matrix[i][k].mul(inverse[k][j]))),if i==j{K::ONE}else{K::ZERO});}}
            determinant=Some(residue(det));
            let data=format!("{{\"name\":\"{name}\",\"z\":{zraw:?},\"rows\":{rows:?},\"columns\":{:?},\"matrix\":{:?},\"inverse\":{:?},\"determinant\":{},\"low_zero\":{},\"universal_root_theorem\":false,\"full_privacy\":false}}\n",piv.iter().map(|&i|columns[i]).collect::<Vec<_>>(),matrix.iter().map(|r|r.iter().copied().map(residue).collect::<Vec<_>>()).collect::<Vec<_>>(),inverse.iter().map(|r|r.iter().copied().map(residue).collect::<Vec<_>>()).collect::<Vec<_>>(),residue(det),root_independent_precondition);
            std::fs::write(out.join(format!("{name}.json")),data).unwrap();
        }
        let summary=format!("{{\"name\":\"{name}\",\"point_low_nonzero\":{low_nonzero:?},\"channel_low_nonzero\":{channel_low:?},\"selected_rank\":{},\"full_rank\":{full_rank},\"normalization_checks\":{normalized_checks},\"nonzero_certificate\":{},\"root_independent_precondition\":{root_independent_precondition}}}",piv.len(),determinant.is_some());
        println!("R118_SOURCE_BOUNDARY {summary}");results.push(summary);
    }
    std::fs::write(out.join("summary.json"),format!("{{\"cases\":[{}],\"actual_two_swap_source\":true,\"accepted_prefix\":false,\"universal_coverage\":false,\"full_security\":false}}\n",results.join(","))).unwrap();
}
