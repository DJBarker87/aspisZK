// Exact reduced causal far-final moments. Derived from the frozen
// helper_ood_strategy.rs preflight; that artifact remains unchanged.
// Fixed C1=0; fixed three helper words; both OOD answer vectors have
// lane0=lane28=1. Their formal scalar-power polynomial is 1+X^28.
// No payment semantics, production dimensions, FS, or QM31 extrapolation.
use std::time::Instant;
const P: usize = 19;
const T: usize = 4;
const NF: usize = P*P;
const QUERIES: u64 = 12*18; // Ordered distinct pairs, then nonzero rho.
const TAIL_DEN: u64 = 19*19*19;
const TAIL_NUM: u64 = TAIL_DEN-13*13*13;
type V8 = [usize;8];
type Final = [usize;2];
type Hist = [u16;P];
type Word = [[usize;4];T];
type Point = (usize,usize);
const OBJECTIVES: usize = 5;
const PREFIXES: usize = 2*2*(P-1)*(P-1)*(P-1);
fn add(a:usize,b:usize)->usize {(a+b)%P}
fn sub(a:usize,b:usize)->usize {(a+P-b)%P}
fn mul(a:usize,b:usize)->usize {a*b%P}
fn pow(mut a:usize,mut n:usize)->usize {let mut r=1;while n>0 {if n&1==1 {r=mul(r,a)}a=mul(a,a);n>>=1}r}
fn inv(a:usize)->usize {assert_ne!(a,0);pow(a,P-2)}
fn eval(c:&[usize],x:usize)->usize {c.iter().rev().fold(0,|a,&v|add(mul(a,x),v))}
fn dot(a:&[usize],b:&[usize])->usize {assert_eq!(a.len(),b.len());a.iter().zip(b).fold(0,|s,(&x,&y)|add(s,mul(x,y)))}
fn slots((x,y):Point)->[Point;4] {[(x,y),(x,sub(0,y)),(sub(0,x),sub(0,y)),(sub(0,x),y)]}
fn points()->[Point;T] {
    let mut seen=[[false;P];P];let mut out=Vec::new();
    for x in 1..P {for y in 1..P {if add(mul(x,x),mul(y,y))==1 && !seen[x][y] {
        out.push((x,y));for (xx,yy) in slots((x,y)) {seen[xx][yy]=true;}
    }}}
    assert_eq!(out.len(),T);out.try_into().unwrap()
}
fn chord(mode:usize)->[usize;3] {
    let (s,t)=if mode==0{((0,1),(0,P-1))}else{((P-1,0),(1,0))};
    for (x,y) in [s,t]{assert_eq!(add(mul(x,x),mul(y,y)),1);}
    let (h0,h1)=if s.0!=t.0{(s.0,t.0)}else{(s.1,t.1)};
    assert_eq!(mul(sub(h0,h1),inv(sub(h0,h1))),1);
    [sub(mul(s.0,t.1),mul(s.1,t.0)),sub(s.1,t.1),sub(t.0,s.0)]
}
fn t2(x:usize)->usize {sub(mul(2,mul(x,x)),1)}
fn basis((x,y):Point)->V8 {let z=t2(x);[1,y,x,mul(x,y),z,mul(y,z),mul(x,z),mul(mul(x,y),z)]}
fn encode(c:&V8,p:Point)->usize {dot(c,&basis(p))}
fn forward(c:&V8,a:usize)->Final {let d=[1,a,pow(a,2),pow(a,3)];[dot(&c[0..4],&d),dot(&c[4..8],&d)]}
fn fold((x,y):Point,v:&[usize;4],a:usize)->usize {
    let left=add(mul(add(v[0],v[1]),inv(2)),mul(a,mul(sub(v[0],v[1]),inv(mul(2,y)))));
    let right=sub(mul(add(v[2],v[3]),inv(2)),mul(a,mul(sub(v[2],v[3]),inv(mul(2,y)))));
    add(mul(add(left,right),inv(2)),mul(pow(a,2),mul(sub(left,right),inv(mul(2,x)))))
}
fn f_eval(f:&Final,p:Point)->usize {add(f[0],mul(t2(p.0),f[1]))}
fn mle(z:[usize;3],i:usize)->usize {(0..3).fold(1,|s,j|mul(s,if i>>j&1==1 {z[j]}else{sub(1,z[j])}))}
fn ordinary(k:usize)->V8 {
    // Reduced product rows, NOT the selected ten-coordinate successor.
    let z=[2,3,4];let next=[3,4,5];let paired=[sub(1,2),sub(1,3),4];
    std::array::from_fn(|i|add(usize::from(i%3==0),add(mul(k,mle(z,i)),
        add(mul(pow(k,2),mle(next,i)),mul(pow(k,3),mle(paired,i))))))
}
fn transpose(mode:usize,w:&V8)->V8 {
    let h=inv(2);let q=inv(4);
    let unit=if mode==0 {[w[2],w[3],mul(h,add(w[0],w[4])),mul(h,add(w[1],w[5])),w[6],w[7],
        add(mul(h,w[4]),mul(q,w[0])),add(mul(h,w[5]),mul(q,w[1]))]}
    else {[w[1],mul(h,sub(w[0],w[4])),w[3],mul(h,sub(w[2],w[6])),w[5],
        sub(mul(h,w[4]),mul(q,w[0])),w[7],sub(mul(h,w[6]),mul(q,w[2]))]};
    // Literal cross-product chords from (0,1),(0,-1) and (-1,0),(1,0).
    unit.map(|v|mul(2,v))
}
// Independent polynomial-pair reference: multiply by x/y first, convert
// degree<=5 polynomials into [1,x,T2,xT2,T4,xT4], then project to8 entries.
fn polynomial_pair(c:&V8)->[[usize;6];2] {
    let b=[[1,0,0,0,0,0],[0,1,0,0,0,0],[P-1,0,2,0,0,0],[0,P-1,0,2,0,0]];
    std::array::from_fn(|parity|std::array::from_fn(|d|(0..4).fold(0,|s,j|add(s,mul(c[2*j+parity],b[j][d])))))
}
fn natural(p:[usize;6])->[usize;6] {
    let c5=mul(p[5],inv(8));let c4=mul(p[4],inv(8));
    let c3=mul(add(p[3],mul(8,c5)),inv(2));let c2=mul(add(p[2],mul(8,c4)),inv(2));
    [sub(add(p[0],c2),c4),sub(add(p[1],c3),c5),c2,c3,c4,c5]
}
fn multiply_reference(mode:usize,c:&V8)->([usize;8],[usize;4]) {
    let p=polynomial_pair(c);let mut result=[[0;6];2];
    if mode==0 {for j in 0..5 {result[0][j+1]=p[0][j];result[1][j+1]=p[1][j];}}
    else {result[1]=p[0];result[0]=p[1];for j in 0..4 {result[0][j+2]=sub(result[0][j+2],p[1][j]);}}
    for row in &mut result {for value in row {*value=mul(2,*value);}}
    let a=natural(result[0]);let b=natural(result[1]);
    (std::array::from_fn(|j|if j%2==0 {a[j/2]}else{b[j/2]}),[a[4],b[4],a[5],b[5]])
}
fn weights(mode:usize,k:usize,tau:usize,a:usize)->Final {
    let mut w=transpose(mode,&ordinary(k));w[7]=add(w[7],tau);
    if mode==0 {w[6]=add(w[6],mul(2,mul(tau,tau)));}else{w[5]=sub(w[5],mul(2,mul(tau,tau)));}
    let d=[1,pow(a,3),pow(a,2),a];[mul(inv(4),dot(&w[0..4],&d)),mul(inv(4),dot(&w[4..8],&d))]
}
fn image(mode:usize,c:&V8)->[usize;2] {[c[7],if mode==0 {mul(2,c[6])}else{sub(0,mul(2,c[5]))}]}
fn raw_helpers(points:&[Point;T],profile:usize)->[Word;3] {
    std::array::from_fn(|lane|std::array::from_fn(|f|std::array::from_fn(|s| {
        let (x,y)=slots(points[f])[s];if profile==0||f!=lane {0}else{
            match lane {0=>add(1,y),1=>mul(x,add(1,y)),_=>mul(add(1,x),add(1,y))}
        }
    })))
}
fn received(points:&[Point;T],helpers:&[Word;3],mode:usize,gamma:usize,ood:usize)->Word {
    let shift=mul(ood,inv(pow(gamma,26)));
    std::array::from_fn(|f|std::array::from_fn(|s|{
        let (x,y)=slots(points[f])[s];let line=mul(2,if mode==0{x}else{y});
        let h=add(helpers[0][f][s],add(mul(gamma,helpers[1][f][s]),mul(pow(gamma,2),helpers[2][f][s])));
        mul(sub(h,shift),inv(line))
    }))
}
fn initial_claim(gamma:usize,k:usize,inactive:usize,ood:usize)->usize {
    // Constant CIRCLE polynomial I=1 has natural coefficient vector e0.
    // Its ordinary functional is w[0], not the sum of the row scales.
    mul(sub(inactive,mul(ood,ordinary(k)[0])),inv(pow(gamma,26)))
}
fn solve(mut a:Vec<Vec<usize>>,n:usize)->Option<Vec<usize>> {
    let mut row=0;let mut pivots=Vec::new();
    for col in 0..n {let Some(p)=(row..a.len()).find(|&r|a[r][col]!=0) else{continue};
        a.swap(row,p);let scale=inv(a[row][col]);for j in col..=n {a[row][j]=mul(a[row][j],scale);}
        for r in 0..a.len(){if r==row{continue}let scale=a[r][col];for j in col..=n{a[r][j]=sub(a[r][j],mul(scale,a[row][j]));}}
        pivots.push(col);row+=1;if row==a.len(){break}
    }
    if a.iter().any(|r|r[..n].iter().all(|&v|v==0)&&r[n]!=0){return None}
    let mut out=vec![0;n];for (r,&col) in pivots.iter().enumerate(){out[col]=a[r][n];}Some(out)
}
fn image_distance(points:&[Point;T],r:&Word,mode:usize)->usize {
    let mut best=T;
    for support in 0usize..1<<T {
        let mut equations=Vec::new();
        for f in 0..T {if support>>f&1==0{continue}for s in 0..4 {
            let mut eq=basis(slots(points[f])[s]).to_vec();eq.push(r[f][s]);equations.push(eq);
        }}
        for index in [7,if mode==0{6}else{5}] {let mut eq=vec![0;9];eq[index]=1;equations.push(eq);}
        if let Some(solution)=solve(equations,8){let c:V8=solution.try_into().unwrap();assert_eq!(image(mode,&c),[0,0]);
            let distance=(0..T).filter(|&f|(0..4).any(|s|encode(&c,slots(points[f])[s])!=r[f][s])).count();
            assert!(distance<=T-support.count_ones() as usize);best=best.min(distance);
        }
    }best
}
struct Tables {hist:Vec<Hist>,far:Vec<bool>,matches:Vec<usize>,folded:Vec<[usize;T]>}
fn tables(points:&[Point;T],r:&Word)->Tables {
    let mut hist=vec![[0;P];P*NF];let mut far=vec![false;P*NF];let mut matches=vec![0;P*NF];let mut folded=Vec::new();
    for a in 0..P {let word: [usize;T]=std::array::from_fn(|f|fold(points[f],&r[f],a));folded.push(word);
        for fi in 0..NF {let f=[fi%P,fi/P];let residual:[usize;T]=std::array::from_fn(|j|sub(f_eval(&f,points[j]),word[j]));
            matches[a*NF+fi]=residual.iter().filter(|&&v|v==0).count();
            far[a*NF+fi]=T-matches[a*NF+fi]>1;
            for i in 0..T {for j in 0..T {if i==j{continue}for rho in 1..P {hist[a*NF+fi][mul(rho,add(residual[i],mul(rho,residual[j])))] +=1;}}}
            assert_eq!(hist[a*NF+fi].iter().map(|&n|n as u64).sum::<u64>(),QUERIES);
        }
    }Tables{hist,far,matches,folded}
}
fn slow_score(points:&[Point;T],table:&Tables,a:usize,f:&Final,prior:usize,w:&Final)->u64 {
    let residual:[usize;T]=std::array::from_fn(|j|sub(f_eval(f,points[j]),table.folded[a][j]));
    let delta=sub(prior,dot(w,f));let mut total=0;
    for i in 0..T {for j in 0..T {if i==j{continue}for rho in 1..P {
        let after=sub(delta,mul(rho,add(residual[i],mul(rho,residual[j]))));
        total+=if after==0 {TAIL_DEN}else{TAIL_NUM};
    }}}total
}
fn tail_certificate()->[usize;7] {
    for mask in 0usize..1<<P {if mask.count_ones()!=6{continue}let mut poly=vec![1];
        for x in 0..P {if mask>>x&1==0{continue}let mut next=vec![0;poly.len()+1];for (j,&v) in poly.iter().enumerate(){next[j]=sub(next[j],mul(x,v));next[j+1]=add(next[j+1],v);}poly=next;}
        let boundary=mul(4,add(poly[0],poly[4]));if boundary==0{continue}
        let result: [usize;7]=std::array::from_fn(|j|mul(poly[j],inv(boundary)));
        for prior in 1..P {let scaled=result.map(|v|mul(v,prior));assert_eq!(mul(4,add(scaled[0],scaled[4])),prior);assert_eq!((0..P).filter(|&x|eval(&scaled,x)==0).count(),6);}
        return result;
    }panic!("missing tail certificate")
}
fn reference_checks(points:&[Point;T])->usize {
    let mut count=0;
    assert_eq!(chord(0),[0,2,0]);assert_eq!(chord(1),[0,0,2]);
    for mode in 0..2 {for k in 1..P {let w=ordinary(k);let fast=transpose(mode,&w);
        for j in 0..8 {let mut e=[0;8];e[j]=1;let (mapped,_)=multiply_reference(mode,&e);assert_eq!(fast[j],dot(&w,&mapped));count+=1;}
        for seed in 0..12 {let mut c:V8=std::array::from_fn(|j|(seed*7+j*j+3*j)%P);c[7]=0;c[if mode==0{6}else{5}]=0;
            let (mapped,omitted)=multiply_reference(mode,&c);assert_eq!(omitted,[0;4]);assert_eq!(dot(&fast,&c),dot(&w,&mapped));
            let mut original=mapped;original[0]=add(original[0],1);
            for gamma in [1,2,3] {let claimed=dot(&w,&original);
                assert_eq!(initial_claim(gamma,k,claimed,1),mul(dot(&fast,&c),inv(pow(gamma,26))));count+=1;}
            for p in points {for (x,y) in slots(*p){let line=mul(2,if mode==0{x}else{y});assert_eq!(encode(&mapped,(x,y)),mul(line,encode(&c,(x,y))));count+=1;}}
        }
    }}
    for j in 0..8 {let mut e=[0;8];e[j]=1;for p in points {let word=slots(*p).map(|s|encode(&e,s));for a in 0..P {assert_eq!(fold(*p,&word,a),f_eval(&forward(&e,a),*p));count+=1;}}}
    count
}

// Both component-OOD vectors are fixed before gamma: false early C1 lane0
// is one, and late helper lane28 is one. Other entries are zero. The
// polynomial degree is 28 before field evaluation; F19 values also obey
// Fermat periodicity, which cannot be extrapolated to QM31.
fn fixed_ood_claims()->[usize;29] {
    let mut c=[0;29];c[0]=1;c[28]=1;c
}
fn ood_batch(gamma:usize)->usize {
    let b=eval(&fixed_ood_claims(),gamma);
    assert_eq!(b,add(1,pow(gamma,28)));
    assert_eq!(mul(b,inv(pow(gamma,26))),add(inv(pow(gamma,26)),pow(gamma,2)));
    b
}
type Values = [[[u64;OBJECTIVES];P];P];
type Scores = [[u64;OBJECTIVES];P];
// Objectives: full acceptance; far full acceptance; relation-compatible
// far pointwise query moment; query-only far moment; prior-zero far full
// acceptance. Each column is optimized by its OWN causal policy.
fn prefix_moments(points:&[Point;T],table:&Tables,mode:usize,k:usize,tau:usize,
    direct:bool)->(Values,u64) {
    let mut out=[[[0;OBJECTIVES];P];P];let mut checks=0;
    for a in 0..P {
        let w=weights(mode,k,tau,a);let mut query_only=0;
        for fi in 0..NF {
            let f=[fi%P,fi/P];let d=dot(&w,&f);
            let h=&table.hist[a*NF+fi];
            let far=table.far[a*NF+fi];
            let m=table.matches[a*NF+fi] as u64;
            let pointwise=m*m.saturating_sub(1)*(P as u64-1)*TAIL_DEN;
            if far {
                query_only=query_only.max(pointwise);
                out[a][d][2]=out[a][d][2].max(pointwise);
                let zero_score=QUERIES*TAIL_NUM+(TAIL_DEN-TAIL_NUM)*h[0] as u64;
                out[a][d][4]=out[a][d][4].max(zero_score);
            }
            for carried in 0..P {
                let delta=sub(carried,d);
                let score=QUERIES*TAIL_NUM+(TAIL_DEN-TAIL_NUM)*h[delta] as u64;
                out[a][carried][0]=out[a][carried][0].max(score);
                if far {out[a][carried][1]=out[a][carried][1].max(score);}
                if direct&&fi%89==0&&carried%7==0 {
                    assert_eq!(score,slow_score(points,table,a,&f,carried,&w));checks+=1;
                }
            }
        }
        for carried in 0..P {
            out[a][carried][3]=query_only;
            assert!(out[a][carried][0]>=out[a][carried][1]);
            assert!(out[a][carried][1]>=out[a][carried][4]);
            assert!(out[a][carried][3]>=out[a][carried][2]);
            assert!(out[a][carried][4]>=out[a][carried][2]);
        }
    }
    (out,checks)
}
fn response(claim:usize,c0:usize,c1:usize,a:usize)->usize {
    add(add(c0,mul(c1,a)),mul(sub(mul(claim,inv(4)),c0),pow(a,4)))
}
fn response_schedules()->Vec<[u8;P]> {
    (0..P*P*P).map(|n|{
        let (claim,c0,c1)=(n/(P*P),n/P%P,n%P);
        assert_eq!(mul(4,add(c0,sub(mul(claim,inv(4)),c0))),claim);
        std::array::from_fn(|a|response(claim,c0,c1,a) as u8)
    }).collect()
}
fn best_responses(v:&Values,schedules:&[[u8;P]])->Scores {
    let mut result=[[0;OBJECTIVES];P];
    for claim in 0..P {for c0 in 0..P {for c1 in 0..P {
        let mut total=[0;OBJECTIVES];
        let response=&schedules[(claim*P+c0)*P+c1];
        // MAX response is outside this fresh-alpha SUM. It cannot depend on alpha.
        for a in 0..P {for objective in 0..OBJECTIVES {
            total[objective]+=v[a][response[a] as usize][objective];
        }}
        for objective in 0..OBJECTIVES {
            result[claim][objective]=result[claim][objective].max(total[objective]);
        }
    }}}
    result
}
fn tail_paths(error:usize,depth:usize,certificate:&[usize;7])->u64 {
    if depth==0 {return u64::from(error==0)}
    // One fixed polynomial, scaled by the CURRENT discrepancy, then fresh
    // alpha. Subsequent response may depend on this observed new error.
    (0..P).map(|a|tail_paths(mul(error,eval(certificate,a)),depth-1,certificate)).sum()
}
fn gcd(mut a:u64,mut b:u64)->u64 {while b!=0 {let r=a%b;a=b;b=r;}a}
fn main() {
    assert_eq!(std::env::args().nth(1).as_deref(),Some("--full-causal"),
        "only the predeclared bounded causal family is enabled");
    let started=Instant::now();let points=points();
    let references=reference_checks(&points);let certificate=tail_certificate();
    for error in 0..P {
        assert_eq!(tail_paths(error,3,&certificate),if error==0 {TAIL_DEN}else{TAIL_NUM});
    }
    let schedules=response_schedules();
    let mut totals=[[0u64;OBJECTIVES];2];
    let mut distances=[[0usize;T+1];2];
    let mut inactive_policies=Vec::new();
    let mut prefix_count=0;let mut scalar_checks=0u64;
    let mut histogram_seconds=0.0;let mut value_seconds=0.0;let mut response_seconds=0.0;
    for profile in 0..2 {
        // This choice is not optimized after any challenge: both fixed
        // helper profiles are reported separately.
        let helpers=raw_helpers(&points,profile);
        for mode in 0..2 {for gamma in 1..P {
            let batch=ood_batch(gamma);
            let word=received(&points,&helpers,mode,gamma,batch);
            let stamp=Instant::now();let table=tables(&points,&word);
            histogram_seconds+=stamp.elapsed().as_secs_f64();
            let distance=image_distance(&points,&word,mode);distances[profile][distance]+=1;
            let mut inactive_scores=[[0u64;OBJECTIVES];P];
            for k in 1..P {for tau in 1..P {
                let stamp=Instant::now();
                let (values,checks)=prefix_moments(&points,&table,mode,k,tau,k==1&&tau==1);
                value_seconds+=stamp.elapsed().as_secs_f64();scalar_checks+=checks;
                let stamp=Instant::now();let best=best_responses(&values,&schedules);
                response_seconds+=stamp.elapsed().as_secs_f64();prefix_count+=1;
                for inactive in 0..P {
                    let claim=initial_claim(gamma,k,inactive,batch);
                    for objective in 0..OBJECTIVES {
                        inactive_scores[inactive][objective]+=best[claim][objective];
                    }
                }
            }}
            let mut choices=[0usize;OBJECTIVES];
            // MAX inactive is outside the kappa/tau SUM, but inside the
            // gamma/ODD-mode SUM, matching the declared fixing boundary.
            for objective in 0..OBJECTIVES {
                let mut best=0;
                for inactive in 0..P {
                    if inactive_scores[inactive][objective]>best {
                        best=inactive_scores[inactive][objective];choices[objective]=inactive;
                    }
                }
                totals[profile][objective]+=best;
            }
            inactive_policies.push([profile,mode,gamma,choices[0],choices[1],choices[2],choices[3],choices[4]]);
            println!("{{\"progress_profile\":{},\"ood_mode\":{},\"gamma\":{},\"image_distance\":{},\"completed_prefixes\":{},\"elapsed_seconds\":{}}}",
                profile,mode,gamma,distance,prefix_count,started.elapsed().as_secs_f64());
        }}
    }
    assert_eq!(prefix_count,PREFIXES);
    // No extra normalization for inactive/response/final: those are causal
    // adversary choices, not independent random variables.
    let denominator=2*18u64*18*18*19*QUERIES*TAIL_DEN;
    assert_eq!(denominator,328333855104);
    for profile in 0..2 {
        assert!(totals[profile][0]>=totals[profile][1]);
        assert!(totals[profile][1]>=totals[profile][4]);
        assert!(totals[profile][4]>=totals[profile][2]);
        assert!(totals[profile][3]>=totals[profile][2]);
        assert!(totals[profile].iter().all(|&value|value<=denominator));
        let fractions:Vec<[u64;2]>=totals[profile].iter().map(|&n|{
            let d=gcd(n,denominator);[n/d,denominator/d]
        }).collect();
        println!("{{\"result_profile\":{},\"objective_order\":[\"full_acceptance\",\"far_full_acceptance\",\"relation_compatible_far_query_moment\",\"query_only_far_moment\",\"prior_zero_far_full_acceptance\"],\"numerators\":{:?},\"common_denominator\":{},\"reduced_fractions\":{:?},\"image_distance_histogram\":{:?}}}",
            profile,totals[profile],denominator,fractions,distances[profile]);
    }
    println!("{{\"mode\":\"restricted_full_causal_exact\",\"field\":19,\"query_count\":2,\"circle_fibres\":{:?},\"ood_claims_lane0_and_lane28\":1,\"formal_claim_polynomial\":\"1+X^28\",\"raw_helper_degree\":2,\"response0_free_coefficients\":[0,1],\"response0_fixed_zero_coefficients\":[2,3,5,6],\"tail_kind\":\"three_abstract_compact_degree6_discrepancy_rounds\",\"tail_certificate\":{:?},\"reference_checks\":{},\"direct_scalar_checks\":{},\"prefix_count\":{},\"final_candidate_count\":{},\"final_prior_pair_count\":{},\"response_candidate_count\":{},\"response_alpha_lookups\":{},\"inactive_policies_profile_mode_gamma_then_objectives\":{:?},\"histogram_seconds\":{},\"value_seconds\":{},\"response_seconds\":{},\"seconds\":{},\"scope\":\"Exact backward induction over every challenge and legal causal choice in this restricted F19 family. Helpers/profiles and false component claims fixed in advance. Separate objective optima need not share a policy. Not all6 first-response coefficients, not arbitrary received helpers, not actual tail dimensions, not payment/production/FS, and no QM31 extrapolation.\"}}",
        points.map(|(x,y)|[x,y]),certificate,references,scalar_checks,prefix_count,
        PREFIXES*P*NF,PREFIXES*P*NF*P,PREFIXES*P*P*P,PREFIXES*P*P*P*P,
        inactive_policies,histogram_seconds,value_seconds,response_seconds,started.elapsed().as_secs_f64());
}

