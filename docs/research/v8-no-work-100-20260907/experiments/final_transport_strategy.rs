// Exact backward induction in an explicitly REDUCED F11 linear-code game.
// New versus radius_strategy.rs: choosing final F changes the carried prior
// by -<dualFold(weight),F>; image weights are active, not orthogonal to finals.
// NOT an Aspis circle domain, payment execution, or QM31 probability bound.
// rustc -O -C overflow-checks=yes final_transport_strategy.rs -o <temporary>
use std::time::Instant;
const P: usize = 11;
const T: usize = 8;
const NF: usize = 14641; // Every four-coefficient final over F11.
const QDEN: u64 = 28 * 10;
const TDEN: u64 = 1331;
const TNUM: u64 = 1206; // 1-(1-6/11)^3, with exact attainability checked.
type Final = [usize; 4];
type Hist = [u16; P];
fn add(a: usize, b: usize) -> usize { (a+b)%P }
fn sub(a: usize, b: usize) -> usize { (a+P-b)%P }
fn mul(a: usize, b: usize) -> usize { a*b%P }
fn pow(mut a: usize, mut n: usize) -> usize {
    let mut r=1; while n>0 { if n&1==1 { r=mul(r,a); } a=mul(a,a); n>>=1; } r
}
fn eval(c: &[usize], x: usize) -> usize {
    c.iter().rev().fold(0, |s,&v| add(mul(s,x),v))
}
fn dot(a: &Final,b: &Final) -> usize {
    a.iter().zip(b).fold(0, |s,(&x,&y)| add(s,mul(x,y)))
}
fn final_at(n: usize) -> Final { [n%P,n/P%P,n/(P*P)%P,n/(P*P*P)%P] }
fn mle(z: [usize;4], i: usize) -> usize {
    (0..4).fold(1, |v,j| mul(v,if (i>>j)&1==1 {z[j]} else {sub(1,z[j])}))
}
fn ordinary(kappa: usize) -> [usize;16] {
    let z=[2,3,4,5]; let successor=[3,4,5,6];
    let xor12=[2,3,sub(1,4),sub(1,5)];
    // These are public product covectors. The second is a fixed distinct
    // product row, NOT the source's optimized successor construction.
    std::array::from_fn(|i| add(mul(kappa,mle(z,i)),
        add(mul(pow(kappa,2),mle(successor,i)),mul(pow(kappa,3),mle(xor12,i)))))
}
fn folded_weight(kappa: usize,tau: usize,alpha: usize) -> Final {
    let w=ordinary(kappa); let ds=[1,pow(alpha,3),pow(alpha,2),alpha];
    let mut out=std::array::from_fn(|j| mul(3,(0..4).fold(0, |s,i|
        add(s,mul(w[4*j+i],ds[i]))))); // 1/4 = 3 in F11.
    // Reduced e15 and b*e14-c*e13 image covectors, with b=1,c=2.
    out[3]=add(out[3],mul(3,add(mul(tau,alpha),
        mul(pow(tau,2),sub(pow(alpha,2),mul(2,pow(alpha,3)))))));
    out
}
fn dense_image_check() {
    for k in 1..P {for t in 1..P {for a in 0..P {
        let mut w=ordinary(k); w[15]=add(w[15],t);
        w[14]=add(w[14],pow(t,2)); w[13]=sub(w[13],mul(2,pow(t,2)));
        let ds=[1,pow(a,3),pow(a,2),a];
        let dense:Final=std::array::from_fn(|j|mul(3,(0..4).fold(0,|s,i|
            add(s,mul(w[4*j+i],ds[i])))));
        assert_eq!(dense,folded_weight(k,t,a));
    }}}
    assert!((1..P).any(|t| folded_weight(1,t,1)!=folded_weight(1,1,1)));
}
fn tail_certificate() -> ([usize;7],usize) {
    // A nonzero degree<=6 polynomial has <=6 roots. Enumerate only the
    // 462 six-root supports to find one with nonzero compact boundary.
    for mask in 0u16..(1u16<<P) { if mask.count_ones()!=6 {continue;}
        let mut c=vec![1];
        for r in 0..P {if mask&(1<<r)==0 {continue;} let mut next=vec![0;c.len()+1];
            for (j,&v) in c.iter().enumerate() {
                next[j]=sub(next[j],mul(r,v)); next[j+1]=add(next[j+1],v);
            } c=next;
        }
        let boundary=mul(4,add(c[0],c[4])); if boundary==0 {continue;}
        let normalized: [usize;7]=std::array::from_fn(|j|mul(c[j],pow(boundary,9)));
        assert_eq!(mul(4,add(normalized[0],normalized[4])),1);
        for prior in 1..P {let scaled=normalized.map(|x|mul(prior,x));
            assert_eq!(mul(4,add(scaled[0],scaled[4])),prior);
            assert_eq!((0..P).filter(|&x|eval(&scaled,x)==0).count(),6);
        }
        assert_eq!(TDEN-TNUM,5u64.pow(3)); return (normalized,mask as usize);
    } panic!("no six-root polynomial with nonzero boundary");
}
fn response_values(claim:usize,c0:usize,c1:usize) -> [usize;P] {
    // Exactly 121 first-response strategies; c2,c3,c5,c6 restricted to zero.
    // All six are free in the later discrepancy rounds, accounted above.
    let c4=sub(mul(claim,3),c0);
    assert_eq!(mul(4,add(c0,c4)),claim);
    std::array::from_fn(|a| add(add(c0,mul(c1,a)),mul(c4,pow(a,4))))
}
fn received(alpha:usize) -> [usize;T] {
    // The two nonzero fibres' fold-basis coefficients [1,x+1,0,0]
    // are fixed before alpha; every other fibre is identically zero.
    std::array::from_fn(|x|if x<2 {add(1,mul(alpha,x+1))} else {0})
}
fn slow_score(alpha:usize,f:&Final,prior:usize,w:&Final,transport:bool) -> u64 {
    let rcv=received(alpha);
    let r:[usize;T]=std::array::from_fn(|x|sub(eval(f,x),rcv[x]));
    let delta=if transport {sub(prior,dot(w,f))} else {prior};
    let mut score=0;
    for i in 0..T {for j in i+1..T {for rho in 1..P {
        let after=sub(delta,mul(rho,add(r[i],mul(rho,r[j]))));
        score+=if after==0 {TDEN} else {TNUM};
    }}} score
}
fn gcd(mut a:u64,mut b:u64)->u64 {while b!=0 {let r=a%b;a=b;b=r;} a}
fn fraction(n:u64,d:u64)->String {let g=gcd(n,d);format!("{{\"numerator\":{},\"denominator\":{},\"display\":{:.12}}}",n/g,d/g,n as f64/d as f64)}
fn main() {
    let start=Instant::now(); dense_image_check(); let (tail,mask)=tail_certificate();
    let finals:Vec<Final>=(0..NF).map(final_at).collect();
    let mut hist=vec![[0u16;P];P*NF];
    let mut far=vec![false;P*NF];
    for alpha in 0..P {let rcv=received(alpha);
        for (fi,f) in finals.iter().enumerate() {
            let residual:[usize;T]=std::array::from_fn(|x|sub(eval(f,x),rcv[x]));
            far[alpha*NF+fi]=residual.iter().filter(|&&r|r!=0).count()>1;
            for i in 0..T {for j in i+1..T {for rho in 1..P {
                let v=mul(rho,add(residual[i],mul(rho,residual[j])));
                hist[alpha*NF+fi][v]+=1;
            }}}
            assert_eq!(hist[alpha*NF+fi].iter().map(|&x|x as u64).sum::<u64>(),QDEN);
        }
    }
    let hist_seconds=start.elapsed().as_secs_f64();
    // mode0 correct transport/all; mode1 correct transport/far;
    // mode2 DELIBERATELY WRONG omitted transport/all; mode3 omitted/far.
    // Averaged tau score per kappa, initial scalar and mode.
    let mut sum_tau=[[[0u64;4];P];P];
    let mut direct_checks=0u64; let mut corrected_best_changes=0u64;
    let mut premature_alpha_gain=[0u64;4];
    for kappa in 1..P {for tau in 1..P {
        let mut values=[[[0u64;4];P];P]; // alpha, prior, mode
        for alpha in 0..P {
            let w=folded_weight(kappa,tau,alpha);
            for (fi,f) in finals.iter().enumerate() {
                let d=dot(&w,f); let h=&hist[alpha*NF+fi];
                let isfar=far[alpha*NF+fi];
                for prior in 0..P {
                    let correct=QDEN*TNUM+(TDEN-TNUM)*h[sub(prior,d)] as u64;
                    let omitted=QDEN*TNUM+(TDEN-TNUM)*h[prior] as u64;
                    let v=&mut values[alpha][prior];
                    v[0]=v[0].max(correct); v[2]=v[2].max(omitted);
                    if isfar {v[1]=v[1].max(correct);v[3]=v[3].max(omitted);}
                    // Independent direct scalar evaluation at a fixed
                    // predeclared grid, never a favorable-policy search.
                    if kappa==1 && tau==1 && fi%997==0 {
                        assert_eq!(correct,slow_score(alpha,f,prior,&w,true));
                        assert_eq!(omitted,slow_score(alpha,f,prior,&w,false));
                        direct_checks+=2;
                    }
                }
            }
            for prior in 0..P { if values[alpha][prior][0]!=values[alpha][prior][2] {
                corrected_best_changes+=1;
            }}
        }
        for claim in 0..P {
            let mut best=[0u64;4];
            for c0 in 0..P {for c1 in 0..P {
                let responses=response_values(claim,c0,c1);
                let mut score=[0u64;4];
                for a in 0..P {for mode in 0..4 {score[mode]+=values[a][responses[a]][mode];}}
                for mode in 0..4 {best[mode]=best[mode].max(score[mode]);}
            }}
            for mode in 0..4 {
                sum_tau[kappa][claim][mode]+=best[mode];
                // Invalid response-after-alpha control. This must only
                // upper-bound the valid causal strategy optimum.
                let premature:u64=(0..P).map(|a|(0..P).map(|p|values[a][p][mode]).max().unwrap()).sum();
                assert!(premature>=best[mode]);
                premature_alpha_gain[mode]+=premature-best[mode];
            }
        }
    }}
    // Fresh gamma, then inactive (chosen after gamma but BEFORE kappa),
    // kappa,tau,response0,alpha,final,queries,rho,three adaptive repairs.
    // Noise gamma^28 is nonzero. Scaling received/finals/responses by its
    // inverse is a bijection of every search class, not security credit.
    let mut totals=[[0u64;4];2]; // honest row claims; false fixed C1 row0=1
    let mut late_inactive=[[0u64;4];2];
    for claim_case in 0..2 {for gamma in 1..P {
        let invnoise=pow(pow(gamma,28),9);
        let mut best=[0u64;4];
        for inactive in 0..P {
            let mut score=[0u64;4];
            for kappa in 1..P {
                let claim=mul(add(inactive,mul(kappa,claim_case)),invnoise);
                for mode in 0..4 {score[mode]+=sum_tau[kappa][claim][mode];}
            }
            for mode in 0..4 {best[mode]=best[mode].max(score[mode]);}
        }
        for mode in 0..4 {
            totals[claim_case][mode]+=best[mode];
            let late:u64=(1..P).map(|k|(0..P).map(|c|sum_tau[k][c][mode]).max().unwrap()).sum();
            assert!(late>=best[mode]); late_inactive[claim_case][mode]+=late;
        }
    }}
    let den=QDEN*TDEN*P as u64*10*10*10;
    println!("{{\"field\":11,\"positions\":8,\"q\":2,\"final_coefficients\":4,");
    println!("\"final_options\":{NF},\"response0_options_per_claim\":121,");
    println!("\"tail_root_polynomial\":{:?},\"tail_root_mask\":{mask},",tail);
    println!("\"tail_nonzero\":{},",fraction(TNUM,TDEN));
    println!("\"modes\":[\"correct_all\",\"correct_distance_gt_1\",\"invalid_omitted_transport_all\",\"invalid_omitted_transport_distance_gt_1\"],");
    for case in 0..2 {
        let name=if case==0 {"honest_point_claims"} else {"fixed_false_C1_row0"};
        println!("\"{name}\":[{}],",totals[case].iter().map(|&n|fraction(n,den)).collect::<Vec<_>>().join(","));
        println!("\"invalid_late_inactive_case{case}\":[{}],",late_inactive[case].iter().map(|&n|fraction(n,den)).collect::<Vec<_>>().join(","));
    }
    println!("\"direct_scalar_checks\":{direct_checks},\"states_with_changed_optimum\":{corrected_best_changes},");
    println!("\"invalid_after_alpha_extra_score\":{:?},",premature_alpha_gain);
    println!("\"histogram_bytes\":{},\"histogram_seconds\":{hist_seconds},\"total_seconds\":{},",hist.len()*std::mem::size_of::<Hist>(),start.elapsed().as_secs_f64());
    println!("\"scope\":\"Exact backward induction within fixed received-word/product-row family and two-free-coefficient first responses; all four final coefficients and all later compact discrepancy responses. Fresh ideal challenges, active reduced image covectors and final-dependent prior. Not an Aspis circle-domain or payment game; no QM31 extrapolation.\"}}");
}
