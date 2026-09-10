//! Small exact countermodel to rank-only row/image shrinkage, NOT a selected
//! higher-factor or payment verifier counterexample. No external dependencies.
use std::collections::BTreeSet;
const P: u64 = 65537;
fn add(a:u64,b:u64)->u64 {(a+b)%P}
fn sub(a:u64,b:u64)->u64 {(a+P-b)%P}
fn mul(a:u64,b:u64)->u64 {a*b%P}
fn pow(mut a:u64,mut n:u64)->u64 {let mut r=1;while n>0 {if n&1!=0 {r=mul(r,a);} a=mul(a,a);n>>=1;}r}
fn inv(a:u64)->u64 {assert_ne!(a,0);pow(a,P-2)}
fn dot(a:&[u64],b:&[u64])->u64 {a.iter().zip(b).fold(0,|s,(&x,&y)|add(s,mul(x,y)))}
fn poly(a:&[u64],x:u64)->u64 {a.iter().rev().fold(0,|s,&v|add(mul(s,x),v))}
fn circle(v:&[u64;8],x:u64,y:u64)->u64 {
    let t2=sub(mul(2,mul(x,x)),1);let basis=[1,x,t2,mul(x,t2)];
    (0..4).fold(0,|s,i|add(s,mul(basis[i],add(v[2*i],mul(y,v[2*i+1])))))
}
// Literal y-low-bit natural4 line basis 1,x,T2,x*T2. Chord D=1-x-y.
fn reconstruct(q:&[u64;8])->[u64;8] {
    let a=[sub(q[0],q[4]),sub(q[2],q[6]),mul(2,q[4]),mul(2,q[6])];
    let b=[sub(q[1],q[5]),sub(q[3],q[7]),mul(2,q[5]),mul(2,q[7])];
    let mut e=[0;6];let mut o=[0;6];
    for i in 0..4 {e[i]=add(e[i],sub(a[i],b[i]));e[i+1]=sub(e[i+1],a[i]);
        e[i+2]=add(e[i+2],b[i]);o[i]=add(o[i],sub(b[i],a[i]));o[i+1]=sub(o[i+1],b[i]);}
    assert_eq!(&e[4..],&[0,0]);assert_eq!(&o[4..],&[0,0]);
    let natural=|m:[u64;6]|[add(m[0],mul(m[2],inv(2))),add(m[1],mul(m[3],inv(2))),mul(m[2],inv(2)),mul(m[3],inv(2))];
    let a=natural(e);let b=natural(o);std::array::from_fn(|i|if i%2==0 {a[i/2]}else{b[i/2]})
}
fn q_from(free:&[u64;6])->[u64;8] {[free[0],free[1],free[2],free[3],free[4],free[5],free[5],0]}
// Exact source v6_statement_points: ten-coordinate successor and XOR 12.
fn points(z:[u64;10])->[[u64;10];3] {
    let mut successor=z;successor[9]=sub(1,z[9]);let mut carry=z[9];
    for i in (0..9).rev(){let both=mul(z[i],carry);successor[i]=sub(add(z[i],carry),mul(2,both));carry=both;}
    let mut xor=z;for i in [7,6] {xor[i]=sub(1,xor[i]);}[z,successor,xor]
}
fn mle(point:&[u64;10],i:usize)->u64 {(0..10).fold(1,|v,j|mul(v,if i&(1<<(9-j))==0 {sub(1,point[j])}else{point[j]}))}
fn roots_poly(nodes:&[u64])->Vec<u64> {let mut a=vec![1];for &g in nodes {let mut b=vec![0;a.len()+1];for i in 0..a.len(){b[i]=sub(b[i],mul(g,a[i]));b[i+1]=add(b[i+1],a[i]);}a=b;}a}
fn main(){
    let z=[2,3,5,7,11,13,17,19,23,29];let pts=points(z);
    let rows:[[u64;8];3]=std::array::from_fn(|r|std::array::from_fn(|i|mle(&pts[r],i)));
    assert!(rows.iter().all(|r|r.iter().all(|&x|x!=0)));
    let mut a=[[0;6];3];for j in 0..6 {let mut u=[0;6];u[j]=1;let v=reconstruct(&q_from(&u));for r in 0..3 {a[r][j]=dot(&rows[r],&v);}}
    let original=a;let mut pivots=Vec::new();let mut rank=0;
    for c in 0..6 {if let Some(pivot)=(rank..3).find(|&r|a[r][c]!=0){a.swap(rank,pivot);let inverse=inv(a[rank][c]);for j in 0..6 {a[rank][j]=mul(a[rank][j],inverse);}
        for r in 0..3 {if r!=rank {let scale=a[r][c];for j in 0..6 {a[r][j]=sub(a[r][j],mul(scale,a[rank][j]));}}}
        pivots.push(c);rank+=1;if rank==3 {break;}}}
    assert_eq!(rank,3);let free=(0..6).find(|c|!pivots.contains(c)).unwrap();let mut u=[0;6];u[free]=1;
    for (r,&pivot) in pivots.iter().enumerate(){u[pivot]=sub(0,a[r][free]);}
    assert!(original.iter().all(|r|dot(r,&u)==0));let q=q_from(&u);let v=reconstruct(&q);
    assert_ne!(v,[0;8]);assert_eq!(q[7],0);assert_eq!(q[6],q[5]);
    assert_eq!(circle(&v,1,0),0);assert_eq!(circle(&v,0,1),0);
    assert!(rows.iter().all(|r|dot(r,&v)==0));
    let mut seen=BTreeSet::new();let mut fibres=Vec::new();
    for t in 1..P {let t2=mul(t,t);let den=add(1,t2);if den==0 {continue;}
        let x=mul(sub(1,t2),inv(den));let y=mul(mul(2,t),inv(den));if x==0||y==0 {continue;}
        let pair=(x.min(P-x),y.min(P-y));if seen.contains(&pair){continue;}
        let (x,y)=pair;let slots=[(x,y),(x,P-y),(P-x,P-y),(P-x,y)];
        if slots.iter().any(|&(a,b)|circle(&v,a,b)==0||sub(sub(1,a),b)==0){continue;}
        for &(a,b) in &slots {assert_eq!(add(mul(a,a),mul(b,b)),1);assert_eq!(circle(&v,a,b),mul(sub(sub(1,a),b),circle(&q,a,b)));}
        seen.insert(pair);fibres.push(slots);if fibres.len()==3700 {break;}}
    assert_eq!(fibres.len(),3700);
    let gamma:Vec<u64>=(1..=37).collect();let mut received=Vec::new();
    for start in 0..37 {let nodes:Vec<u64>=(0..29).map(|i|gamma[(start+i)%37]).collect();let h=roots_poly(&nodes);
        assert_eq!(h[29],1);let r:Vec<u64>=h[..29].iter().map(|&x|sub(0,x)).collect();received.push(r);}
    for i in 0..37 {for j in 0..i {assert_ne!(&received[i][..26],&received[j][..26]);}}
    for &g in &gamma {let cg=pow(g,29);let mut full=0;
        for (i,slots) in fibres.iter().enumerate(){let r=&received[i/100];let rg=poly(r,g);let mut matching=true;
            for &(x,y) in slots {let vx=circle(&v,x,y);let raw=poly(&r.iter().map(|&c|mul(c,vx)).collect::<Vec<_>>(),g);
                assert_eq!(raw,mul(rg,vx));let virtual_q=mul(raw,inv(sub(sub(1,x),y)));
                matching &= virtual_q==mul(cg,circle(&q,x,y));}
            if matching {full+=1;}}
        assert_eq!(full,2900);assert!(200808*3700<=full*262144 && full*262144<=252847*3700);
        for row in &rows {assert_eq!(mul(cg,dot(row,&v)),0);}
    }
    // Max 8 zeros for a nonzero natural8 circle function: <=8 own symbols
    // per group, unless one group determines all 26 C1 component messages.
    assert!(37*8<=400);assert!(400*1048576u64<38228*14800u64);
    println!("PASS field={} gamma_nodes=37 fibres=3700 symbols=14800 per_gamma_full_fibres=2900",P);
    println!("source_related_MLE_rows={:?} rank={} free_image_dimension={} quotient={:?} original={:?}",pts,rank,6-rank,q,v);
    println!("PASS all_37_nodes_row_correct=true image=true OOD_zero=true received_gamma_degree_le28=true candidate_gamma_degree=29 helper_GRS_degree=2");
    println!("PASS checked_original_and_quotient_symbol_cases={} group_own_bound=400 scaled_early_threshold_gt400=true",37*14800);
    println!("SCOPE natural8 circle subcode, exact ten-bit source-related MLE rows at a fixed guessed prefix; NOT selected QM31 encoder, retained prime factor, canonical interpolant, sampler probability, authentication, semantic/payment acceptance, or 34810510 counterexample");
}
