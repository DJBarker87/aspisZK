// Restricted exact F127 regression. No transcript, cryptographic or payment code.
// Exhausts all coordinates/challenges for this ONE fixed cubic, and all degree<=2
// scalar codewords for the three distinct received C1 lane patterns.
use std::time::Instant;

const P: i64 = 127;
type Poly = Vec<i64>;
fn red(a: i64) -> i64 { a.rem_euclid(P) }
fn trim(mut a: Poly) -> Poly {
    while a.last() == Some(&0) { a.pop(); }
    a
}
fn add(a: &Poly, b: &Poly) -> Poly {
    let mut c = vec![0; a.len().max(b.len())];
    for (i, &x) in a.iter().enumerate() { c[i] = red(c[i] + x); }
    for (i, &x) in b.iter().enumerate() { c[i] = red(c[i] + x); }
    trim(c)
}
fn scale(a: &Poly, c: i64) -> Poly { trim(a.iter().map(|&x| red(c*x)).collect()) }
fn sub(a: &Poly, b: &Poly) -> Poly { add(a, &scale(b, -1)) }
fn mul(a: &Poly, b: &Poly) -> Poly {
    if a.is_empty() || b.is_empty() { return vec![]; }
    let mut c = vec![0; a.len()+b.len()-1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() { c[i+j] = red(c[i+j]+x*y); }
    }
    trim(c)
}
fn pow(a: &Poly, n: usize) -> Poly {
    let mut result = vec![1];
    for _ in 0..n { result = mul(&result, a); }
    result
}
fn eval(a: &Poly, x: i64) -> i64 {
    a.iter().rev().fold(0, |r, &c| red(r*x+c))
}
fn scalar_pow(x: i64, n: usize) -> i64 {
    (0..n).fold(1, |a, _| red(a*x))
}
fn choose(n: usize, k: usize) -> i64 {
    if k>n { return 0; }
    let mut c = 1i64;
    for j in 0..k { c=c*(n-j) as i64/(j+1) as i64; }
    c
}
fn hasse(a: &Poly, x: i64, j: usize) -> i64 {
    red(a.iter().enumerate().skip(j)
        .map(|(n,&c)| c*choose(n,j)*scalar_pow(x,n-j)).sum())
}

// Order<3 bivariate jets in (X-x,Y-received(Z)); coefficients are Z-polynomials.
const EXP: [(usize,usize);6] = [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)];
type Jet = [Poly;6];
fn jet_mul(a: &Jet, b: &Jet) -> Jet {
    let mut out: Jet = std::array::from_fn(|_| vec![]);
    for i in 0..6 { for j in 0..6 {
        let e = (EXP[i].0+EXP[j].0,EXP[i].1+EXP[j].1);
        if e.0+e.1<3 {
            let k=EXP.iter().position(|&v|v==e).unwrap();
            out[k]=add(&out[k],&mul(&a[i],&b[j]));
        }
    }}
    out
}

fn threshold_ledger() {
    let p=(1u128<<31)-1;
    let gamma=p.pow(4)-1;
    let m=gamma/(1u128<<100);
    let (w,t,a)=(117077u128,1048576u128,38230u128);
    let bmax=((m+1)*a-w*t-1)/(m+1-w);
    let cap=|b:u128|w*(t-b)/(a-b);
    assert_eq!(m,16777215);
    assert_eq!(bmax,31129);
    assert_eq!(cap(0),3211198);
    assert_eq!(cap(bmax),16775051);
    assert_eq!(cap(bmax+1),16777397);
    assert!(cap(bmax)*(1u128<<100)<=gamma);
    assert!(cap(bmax+1)*(1u128<<100)>gamma);
    println!("UNIFORM_GAMMA_CARD={gamma}");
    println!("MAX_100_RAW_BIT_GAMMAS={m}");
    println!("MAX_CERTIFIED_IDENTITY_COUNT={bmax}");
    println!("CAP_AT_THRESHOLD={}\nCAP_AFTER_THRESHOLD={}",cap(bmax),cap(bmax+1));
    println!("EARLY_C1_MAX_BAD_SYMBOLS={}",4*16535);
}

fn main() {
    let started=Instant::now();
    threshold_ledger();
    let b=[2i64,3,4];
    let ood=[1i64,8];
    let mut d=b.to_vec();
    d.extend((1..P).filter(|x|!b.contains(x)&&!ood.contains(x)).take(97));
    assert_eq!(d.len(),100);
    let mut v=vec![1];
    for &r in b.iter().chain(ood.iter()) { v=mul(&v,&vec![red(-r),1]); }
    let h=add(&vec![1],&v);
    assert_eq!(h,vec![63,43,51,115,109,1]);
    assert_eq!(h.len()-1,5);
    assert_ne!((h.len()-1)%3,0);
    assert!(d.iter().all(|&x|eval(&h,x)!=0));
    assert!(ood.iter().all(|&x|eval(&h,x)==1));
    let r=vec![0,126,1]; // R(Z)=Z(Z-1), in low C1 lanes 1 and 2; helpers zero.
    let r3=pow(&r,3);
    let mut identities=vec![];
    let mut value_checks=0u64;
    let mut kernel_checks=0u64;
    let mut zero_candidate_checks=0u64;
    for &x in &d {
        let raw=if b.contains(&x) { r.clone() } else { vec![] };
        let residual=sub(&pow(&raw,3),&scale(&r3,eval(&h,x)));
        assert_eq!(residual.is_empty(),b.contains(&x));
        if residual.is_empty() { identities.push(x); }
        for z in 0..P {
            let pointwise=red(scalar_pow(eval(&raw,z),3)
                -scalar_pow(z,3)*scalar_pow(z-1,3)*eval(&h,x));
            assert_eq!(eval(&residual,z),pointwise);
            if !b.contains(&x) { assert_eq!(pointwise==0,z==0||z==1); }
            value_checks+=1;
        }
        assert_eq!(eval(&raw,1),0);
        assert_eq!(eval(&residual,1),0);
        zero_candidate_checks+=1;
        let mut fj:Jet=std::array::from_fn(|_|vec![]);
        fj[0]=residual;
        fj[1]=scale(&r3,-hasse(&h,x,1));
        fj[2]=scale(&pow(&raw,2),3);
        fj[3]=scale(&r3,-hasse(&h,x,2));
        fj[5]=scale(&raw,3);
        let mut y3:Jet=std::array::from_fn(|_|vec![]);
        y3[0]=pow(&raw,3);
        y3[2]=scale(&pow(&raw,2),3);
        y3[5]=scale(&raw,3);
        // P=F^3*Y^3 has all six total-order<3 Hasse coefficients zero.
        let pj=jet_mul(&jet_mul(&jet_mul(&fj,&fj),&fj),&y3);
        for coefficient in &pj { assert!(coefficient.is_empty()); kernel_checks+=1; }
    }
    assert_eq!(identities,b);
    let mut ood_value_checks=0u64;
    for &t in &ood {
        assert!(sub(&r3,&scale(&r3,eval(&h,t))).is_empty());
        for z in 0..P {
            assert_eq!(red(scalar_pow(eval(&r,z),3)
                -scalar_pow(z,3)*scalar_pow(z-1,3)*eval(&h,t)),0);
            ood_value_checks+=1;
        }
    }
    let own=d.chunks_exact(4).filter(|xs|xs.iter().all(|x|!b.contains(x))).count();
    assert_eq!(own,24);
    assert_eq!((245609usize*25).div_ceil(262144),24);
    assert!(identities.iter().all(|x|b.contains(x)));
    // Exhaustively verify the zero message is the unique degree<=2 codeword
    // reaching24/25 complete fibres, for each distinct C1 received-lane pattern.
    let mut codeword_checks=0u64;
    for lane_sign in [-1i64,1,0] {
        let mut qualifying=vec![];
        for c0 in 0..P { for c1 in 0..P { for c2 in 0..P {
            let mut misses=0;
            for xs in d.chunks_exact(4) {
                if xs.iter().any(|&x|red(c0+x*(c1+x*c2))
                    !=if b.contains(&x) {red(lane_sign)} else {0}) {
                    misses+=1;
                    if misses>1 { break; }
                }
            }
            if misses<=1 { qualifying.push([c0,c1,c2]); }
            codeword_checks+=1;
        }}}
        assert_eq!(qualifying,vec![[0,0,0]]);
    }
    assert_eq!(codeword_checks,3*(P as u64).pow(3));
    println!("FIELD=127\nDOMAIN_SYMBOLS=100\nTOTAL_FIBRES=25\nEARLY_ZERO_OWN_FIBRES={own}");
    println!("IDENTITY_COORDINATES={identities:?}\nIDENTITY_INTERSECTION_EARLY_OWN=0");
    println!("OOD_PARAMETERS={ood:?}\nH_ASCENDING_COEFFICIENTS={h:?}");
    println!("PULLBACK_VALUE_CHECKS={value_checks}\nOOD_VALUE_CHECKS={ood_value_checks}");
    println!("KERNEL_HASSE_COEFFICIENT_CHECKS={kernel_checks}");
    println!("ZERO_CANDIDATE_GAMMA1_CHECKS={zero_candidate_checks}");
    println!("DEGREE2_C1_CODEWORD_CHECKS={codeword_checks}");
    println!("SCOPE=one_fixed_F127_cubic_and_three_exhausted_degree2_lane_patterns");
    println!("NOT_PROVED=selected_interpolant_choice,actual_circle_encoder,source_acceptance,OOD_sampler_probability,payment");
    println!("CONTROL_WALL_SECONDS={:.6}",started.elapsed().as_secs_f64());
    println!("RESULT=PASS");
}
