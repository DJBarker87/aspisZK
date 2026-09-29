//! A fixed high-coordinate witness; source equality checks are not a sampler law.
include!("r37_residual_arithmetic.rs");
fn base(n:u32)->K{K::ONE.mul_m31(M31(n))}
fn residue(v:K)->u32{let mut b=[0;16];v.write_le_bytes(&mut b);assert_eq!(&b[4..],&[0;12]);u32::from_le_bytes(b[..4].try_into().unwrap())}
fn pivots(mut a:Vec<Vec<K>>)->Vec<usize>{let mut out=Vec::new();for c in 0..a[0].len(){let r=out.len();let Some(p)=(r..a.len()).find(|&i|a[i][c]!=K::ZERO)else{continue};a.swap(r,p);let inv=a[r][c].inv();for j in c..a[0].len(){a[r][j]=a[r][j].mul(inv);}for i in 0..a.len(){if i==r{continue;}let s=a[i][c];for j in c..a[0].len(){a[i][j]=a[i][j].sub(s.mul(a[r][j]));}}out.push(c);if out.len()==a.len(){break;}}out}
fn make_q(v:&[K],slot:usize)->Vec<K>{let mut q=vec![K::ZERO;1024];for(j,&a)in v.iter().enumerate(){q[4*j+slot]=a;q[4*j]=base(7).pow(slot as u64).mul(a).neg();}q}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),2);let out=std::path::Path::new(&args[1]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    let z=std::array::from_fn(|i|if i==9{base(2)}else if (100>>(9-i))&1==0{K::ZERO}else{K::ONE});let abc=[base(7),base(5),base(5).neg()];let map=basis_transport::transport();
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let weights:Vec<Vec<K>>=points.iter().map(|s|{let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,s.to_vec()).unwrap();(0..1024).map(|i|w.weight_at(i)).collect()}).collect();
    let ew:Vec<_>=weights.iter().map(|w|opening_weights::chord_transpose(&map.dual(w),abc)).collect();
    for r in 0..1024 {
        let c=|j|centry(r,j,abc);
        let expected=[c(101).mul(base(2)).sub(c(100)),c(100).mul(base(2)).neg().add(c(101)).add(c(102).mul(base(4))).sub(c(103).mul(base(2))),c(105).mul(base(2)).sub(c(104))];
        for i in 0..3{assert_eq!(ew[i][r],expected[i]);if r<88{assert_eq!(ew[i][r],K::ZERO);}}
    }
    let rw=opening_weights::quotient_weights(&z,base(5),abc,base(17),false);let gw=opening_weights::quotient_weights(&z,base(5),abc,base(17),true);
    for r in 0..128 {assert_eq!(rw.weight_at(r),base(5).mul(ew[0][r]).add(base(25).mul(ew[1][r])).add(base(125).mul(ew[2][r])));
        assert_eq!(gw.weight_at(r),base(25).mul(ew[1][r]).add(base(125).mul(ew[2][r])).add(base(5).mul(K::ONE.mul_m31(M31_HALF).pow(10)).mul(centry(r,128,abc))));}
    let mut omitted=WeightAccumulator::empty(10);omitted.add_dense((0..1024).map(|r|base(25).mul(ew[1][r]).add(base(125).mul(ew[2][r]))).collect()).unwrap();
    let mut last=vec![K::ZERO;32];last[31]=K::ONE;let last_q=make_q(&last,3);
    let actual_poly=polynomial_for_extension(&last_q,&gw);let wrong_poly=polynomial_for_extension(&last_q,&omitted);
    let omitted_negative=actual_poly.iter().zip(&wrong_poly).filter(|(a,b)|a!=b).count();assert_eq!(omitted_negative,3);
    let observe=|q:&Vec<K>|{let code=chord(q,abc);assert!(code[131..].iter().all(|&v|v==K::ZERO));let original=map.inverse(&code);assert!(structured_g::mixed_coins(&original).iter().all(|&v|v==K::ZERO));let mut o=vec![K::ZERO,dot(&original,&weights[1]),dot(&original,&weights[2])];o.extend(polynomial_for_extension(q,&rw));o.extend(polynomial_for_extension(q,&gw));o};
    let columns:Vec<usize>=(0..27).chain([29]).collect();let rows=[1,2,3,4,5,6,7,8,10,11,12,13,15];let mut os=Vec::new();
    for &c in &columns{let mut v=vec![K::ZERO;32];v[22+c/3]=K::ONE;os.push(observe(&make_q(&v,c%3+1)));}
    let all:Vec<Vec<K>>=rows.iter().map(|&r|os.iter().map(|o|o[r]).collect()).collect();let selected=pivots(all.clone());assert_eq!(selected.len(),13);assert!(selected.contains(&27));
    let mut a:Vec<Vec<K>>=all.iter().map(|r|selected.iter().map(|&c|r[c]).collect()).collect();let matrix=a.clone();let mut inverse=vec![vec![K::ZERO;13];13];for i in 0..13{inverse[i][i]=K::ONE;}
    let mut det=K::ONE;
    for c in 0..13{let p=(c..13).find(|&r|a[r][c]!=K::ZERO).unwrap();if p!=c{a.swap(c,p);inverse.swap(c,p);det=det.neg();}det=det.mul(a[c][c]);let scale=a[c][c].inv();for j in 0..13{a[c][j]=a[c][j].mul(scale);inverse[c][j]=inverse[c][j].mul(scale);}for r in 0..13{if r==c{continue;}let f=a[r][c];for j in 0..13{a[r][j]=a[r][j].sub(f.mul(a[c][j]));inverse[r][j]=inverse[r][j].sub(f.mul(inverse[c][j]));}}}
    for i in 0..13{for j in 0..13{assert_eq!((0..13).fold(K::ZERO,|s,k|s.add(matrix[i][k].mul(inverse[k][j]))),if i==j{K::ONE}else{K::ZERO});}}
    let families:Vec<Vec<u32>>=vec![(0..22).collect(),(0..22).map(|i|2*i).collect(),(0..11).flat_map(|i|[2*i*997,2*i*997+1]).collect(),(0..20).chain([1000,1001]).collect()];
    let mut checks=0;let mut changed=0;
    for queries in families {
        let mut p=vec![K::ONE];for pt in corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap(){let root=pt.x.mul(pt.x).double().sub(M31::ONE);let mut next=times_x(&p);for i in 0..p.len(){next[i]=next[i].sub(p[i].mul_m31(root));}p=next;}
        let mut shifts=vec![p.clone()];for j in 1..10{shifts.push(times_x(&shifts[j-1]));}
        for (at,&c) in columns.iter().enumerate(){let d=22+c/3;let mut rem=vec![K::ZERO;32];rem[d]=K::ONE;
            for top in (22..=d).rev(){let f=rem[top].mul(shifts[top-22][top].inv());for j in 0..=top{rem[j]=rem[j].sub(f.mul(shifts[top-22][j]));}}
            assert!(rem[22..].iter().all(|&v|v==K::ZERO));assert!(rem[..22].iter().any(|&v|v!=K::ZERO));
            let mut v:Vec<_>=rem.iter().map(|v|v.neg()).collect();v[d]=K::ONE;let corrected=make_q(&v,c%3+1);let mut unit=vec![K::ZERO;32];unit[d]=K::ONE;let direct=make_q(&unit,c%3+1);
            assert_eq!(&corrected[88..],&direct[88..]);changed+=corrected[..88].iter().zip(&direct[..88]).filter(|(a,b)|a!=b).count();assert_eq!(observe(&corrected),os[at]);checks+=17;
        }
    }
    let data=format!("{{\"z\":{:?},\"selected_columns\":{:?},\"selected_kernel_columns\":{:?},\"selected_rows\":{:?},\"weights\":{:?},\"matrix\":{:?},\"inverse\":{:?},\"determinant\":{},\"source_entry_checks\":{},\"changed_low_coordinates\":{},\"universal_root_theorem\":false,\"full_privacy\":false}}\n",z.iter().map(|&v|residue(v)).collect::<Vec<_>>(),selected,selected.iter().map(|&i|columns[i]).collect::<Vec<_>>(),rows,ew.iter().map(|w|w[..128].iter().map(|&v|residue(v)).collect::<Vec<_>>()).collect::<Vec<_>>(),matrix.iter().map(|r|r.iter().map(|&v|residue(v)).collect::<Vec<_>>()).collect::<Vec<_>>(),inverse.iter().map(|r|r.iter().map(|&v|residue(v)).collect::<Vec<_>>()).collect::<Vec<_>>(),residue(det),checks,changed);
    std::fs::write(out.join("witness.json"),data).unwrap();println!("R43_UNIVERSAL_WITNESS rank=13 determinant={} selected={:?} source_weight_checks=3072 low_functional_checks=256 omitted_boundary_negative={omitted_negative} normalized_columns=112 observation_checks={checks} changed_low_coordinates={changed} universal_root_theorem=false full_privacy=false",residue(det),selected.iter().map(|&i|columns[i]).collect::<Vec<_>>());
}
