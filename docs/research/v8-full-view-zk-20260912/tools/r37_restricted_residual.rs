//! Uses the exact R36 arithmetic mirror, generated verbatim before its main.
include!("r37_residual_arithmetic.rs");
const ROWS:[usize;13]=[1,2,3,4,5,6,7,8,10,11,12,13,15];
fn root_run(roots:&[K;22])->[K;27]{let mut p=[K::ZERO;27];p[0]=K::ONE;for &root in roots{p=std::array::from_fn(|r|(0..27).fold(K::ZERO,|s,j|s.add(p[j].mul(xentry(j,r)))).sub(root.mul(p[r])));}p}
fn matrix(z:&[K;10],k:K,alpha:K,u:K,v:K,roots:&[K;22])->Vec<Vec<K>>{
    let abc=[K::ONE.add(u.mul(v)),u.mul(v).sub(K::ONE),u.add(v).neg()];let p=root_run(roots);assert!(p[23..].iter().all(|&v|v==K::ZERO));assert_eq!(p[22],K::ONE.mul_m31(M31_HALF).pow(19));
    let mut ew=[[K::ZERO;108];3];for which in 0..3{let z1=point(z,which);let code:[K;111]=std::array::from_fn(|j|tensor(&z1,fixed::ORDER[j]).sub(if fixed::INACTIVE[fixed::ORDER[j]]{tensor(&z1,1023)}else{K::ZERO}));for r in 0..108{ew[which][r]=(0..111).fold(K::ZERO,|s,j|s.add(code[j].mul(centry(r,j,abc))));}}
    let wr=std::array::from_fn(|r|k.mul(ew[0][r]).add(k.pow(2).mul(ew[1][r])).add(k.pow(3).mul(ew[2][r])));let wg=std::array::from_fn(|r|k.pow(2).mul(ew[1][r]).add(k.pow(3).mul(ew[2][r])));
    let mut out=vec![vec![K::ZERO;13];13];for col in 0..13{let q=quotient(&p[..23],col,alpha);let mut obs=vec![K::ZERO,dot(&q,&ew[1]),dot(&q,&ew[2])];obs.extend(poly(&q,&wr,true));obs.extend(poly(&q,&wg,true));for(i,&r)in ROWS.iter().enumerate(){out[i][col]=obs[r];}}out
}
fn determinant(mut a:Vec<Vec<K>>)->K{let mut d=K::ONE;for j in 0..13{let Some(p)=(j..13).find(|&i|a[i][j]!=K::ZERO)else{return K::ZERO};if p!=j{a.swap(p,j);d=d.neg();}let v=a[j][j];d=d.mul(v);let inv=v.inv();for i in j+1..13{let s=a[i][j].mul(inv);for h in j+1..13{a[i][h]=a[i][h].sub(s.mul(a[j][h]));}}}d}
fn encode(a:&[Vec<K>])->Vec<u8>{let mut out=Vec::new();for row in a{for v in row{let mut b=[0;16];v.write_le_bytes(&mut b);out.extend(b);}}out}
fn base(n:u32)->K{K::ONE.mul_m31(M31(n))}
fn main(){
    let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),3);let stage=std::path::Path::new(&args[1]);let out=std::path::Path::new(&args[2]);assert!(!out.exists());std::fs::create_dir(out).unwrap();
    for world in 0..2{let bytes=std::fs::read(stage.join(format!("world{world}-prefix.bin"))).unwrap();assert_eq!(bytes.len(),424);let f:Vec<_>=bytes[..336].chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();let z:[K;10]=f[..10].try_into().unwrap();let queries:Vec<_>=bytes[336..].chunks_exact(4).map(|b|u32::from_le_bytes(b.try_into().unwrap())).collect();let points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();let roots:[K;22]=std::array::from_fn(|i|K::ONE.mul_m31(points[i].x.mul(points[i].x).double().sub(M31::ONE)));
        let u=f[14].mul(K::ONE.add(f[13]).inv());let v=f[16].mul(K::ONE.add(f[15]).inv());let du=K::ONE.add(u.mul(u));let dv=K::ONE.add(v.mul(v));assert_ne!(du,K::ZERO);assert_ne!(dv,K::ZERO);assert_ne!(u,v);let scale=v.sub(u).add(v.sub(u)).mul(du.mul(dv).inv());
        let mut source_p=vec![K::ONE];for &r in &roots{let mut n=times_x(&source_p);for j in 0..source_p.len(){n[j]=n[j].sub(r.mul(source_p[j]));}source_p=n;}let p=root_run(&roots);assert_eq!(source_p.as_slice(),&p[..23]);
        let m=matrix(&z,f[10],f[12],u,v,&roots);let old=std::fs::read(stage.join(format!("world{world}-minor.bin"))).unwrap();let values:Vec<_>=old.chunks_exact(16).map(|b|K::from_le_bytes(b).unwrap()).collect();assert_eq!(values.len(),169);let actual:Vec<Vec<_>>=values.chunks_exact(13).map(|v|v.to_vec()).collect();for i in 0..13{for j in 0..13{assert_eq!(actual[i][j],scale.mul(m[i][j]));}}let d=determinant(m.clone());assert_ne!(d,K::ZERO);assert_eq!(determinant(actual.clone()),scale.pow(13).mul(d));assert_ne!(actual,m);std::fs::write(out.join(format!("world{world}-normalized.bin")),encode(&m)).unwrap();
    }
    // A fixed algebraic witness, deliberately NOT a source-prefix fixture.
    // It obeys root construction and normalized-circle substitution; the roots
    // need not belong to the sampler's domain to witness a formal polynomial.
    let z=std::array::from_fn(|i|base(i as u32+2));let roots=std::array::from_fn(|i|base(i as u32+1));let m=matrix(&z,base(5),base(7),base(2),base(3),&roots);let d=determinant(m.clone());assert_ne!(d,K::ZERO,"explicit algebraic specialization was singular");let mut db=[0;16];d.write_le_bytes(&mut db);assert!(db[4..].iter().all(|&v|v==0));let residue=u32::from_le_bytes(db[..4].try_into().unwrap());std::fs::write(out.join("algebraic-witness-minor.bin"),encode(&m)).unwrap();
    std::fs::write(out.join("summary.json"),format!("{{\"actual_prefixes\":2,\"root_coefficient_checks\":46,\"scaled_minor_checks\":338,\"determinant_scale_exponent\":13,\"algebraic_witnesses\":1,\"algebraic_witness_determinant_m31\":{residue},\"algebraic_witness_source_prefix\":false,\"nonzero_kernel_certificate\":false,\"full_privacy\":false}}\n")).unwrap();println!("R37_RESTRICTED_RESIDUAL prefixes=2 root_coefficients=46 scaled_entries=338 algebraic_witness_det={residue} kernel_certificate=false full_privacy=false");
}
