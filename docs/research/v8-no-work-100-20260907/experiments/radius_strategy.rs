// Exact backward induction in a REDUCED field/domain game, never QM31 rates.
// F11; actual six-sent-coefficient compact boundary 4*(c0+c4)=prior.
// Fixed precommitted four-slot words; final chosen after alpha, before queries.
// Tail scalar error polynomials model all compact replies, adaptively.
const P:usize=11;
fn add(a:usize,b:usize)->usize{(a+b)%P}
fn sub(a:usize,b:usize)->usize{(a+P-b)%P}
fn mul(a:usize,b:usize)->usize{a*b%P}
fn pow(mut a:usize,mut n:usize)->usize{let mut r=1;while n>0{if n&1==1{r=mul(r,a)}a=mul(a,a);n>>=1;}r}
const T:usize=8;
const S:usize=2;
fn bases()->[[usize;P];6]{
    [0,1,2,3,5,6].map(|j|std::array::from_fn(|a|if j==0{sub(1,pow(a,4))}else{pow(a,j)}))
}
fn each_response(prior:usize,mut consume:impl FnMut(&[usize;P])){
    let basis=bases();let mut digits=[0;6];
    let mut values=std::array::from_fn(|a|mul(mul(prior,3),pow(a,4))); // 4^-1=3
    for index in 0..P.pow(6){
        consume(&values);
        if index+1==P.pow(6){break}
        for j in 0..6{
            for a in 0..P{values[a]=add(values[a],basis[j][a]);}
            digits[j]+=1;if digits[j]<P{break}digits[j]=0;
        }
    }
}
fn main(){
    let start=std::time::Instant::now();
    let mut geometry_checks=0u64;
    for word in 0..5usize.pow(6){
        let r:[usize;6]=std::array::from_fn(|j|word/5usize.pow(j as u32)%5);
        for anchor in 0..5{let s=r.iter().filter(|&&v|v!=anchor).count();
            for other in 0..5{if other==anchor{continue}
                let dist=r.iter().filter(|&&v|v!=other).count();
                assert!(6<=s+dist);if 2*s<6{assert!(s<dist)}geometry_checks+=1;
            }
        }
    }
    assert_eq!((1..P).filter(|&rho|sub(2,mul(rho,sub(3,rho)))==0).count(),2);
    let mut roots=0;
    each_response(1,|values|roots=roots.max(values.iter().filter(|&&x|x==0).count()));
    assert_eq!(roots,6);
    // All nonzero prior states are related by scalar multiplication.
    // Honest zero replies keep prior zero; optimum repairs are attainable.
    let denom=P.pow(3) as u64;
    let tail_nonzero=(P.pow(3)-(P-roots).pow(3)) as u64;
    let mut value=[[0u64;P];P];
    let mut chosen=[[(0usize,0usize);P];P];
    let mut query_miss=0usize;
    for i in 0..T{for j in i+1..T{if i>=S&&j>=S{query_miss+=1}}}
    assert_eq!(query_miss,15);
    // Noise on exactly two fibres is fixed BEFORE alpha. Low-bit four-slot
    // map here is invertible; slots correspond to coefficient [1,i+1,0,0].
    // This is an abstract fold model, not the Aspis circle domain.
    for a in 0..P{
        let received:[usize;T]=std::array::from_fn(|x|if x<S{add(1,mul(a,x+1))}else{0});
        for prior in 0..P{for f0 in 0..P{for f1 in 0..P{
            let residual:[usize;T]=std::array::from_fn(|x|sub(add(f0,mul(f1,x)),received[x]));
            let mut score=0;
            for i in 0..T{for j in i+1..T{for rho in 1..P{
                // prior - rho*(r0+rho*r1): degree q=2.
                let delta=sub(prior,mul(rho,add(residual[i],mul(rho,residual[j]))));
                score+=if delta==0{denom}else{tail_nonzero};
            }}}
            if score>value[a][prior]{value[a][prior]=score;chosen[a][prior]=(f0,f1);}
        }}}
    }
    let mut best=[0u64;P];let mut strategies=0u64;
    for prior in 0..P{
        each_response(prior,|values|{
            let score=(0..P).map(|a|value[a][values[a]]).sum::<u64>();
            best[prior]=best[prior].max(score);strategies+=1;
        });
    }
    let first_den=(P*((T*(T-1))/2)*(P-1)) as u64*denom;
    println!("{{");
    println!("\"geometry_checks\":{geometry_checks},");
    println!("\"field\":11,\"domain\":8,\"q\":2,\"corrupt_fibres\":2,");
    println!("\"response0_strategies_enumerated\":{strategies},\"tail_root_max\":{roots},");
    println!("\"tail_nonzero_numerator\":{tail_nonzero},\"tail_denominator\":{denom},");
    println!("\"optimal_suffix_by_prior\":{:?},\"suffix_denominator\":{first_den},",best);
    // Fresh tau mixes image covectors, both target image values are zero.
    // Restricted finals have support only at indices0,1, while carried image
    // after first fold is supported at255, so true prior is unchanged by tau.
    // Responses are allowed to depend on tau; their optimum is the same.
    let row_cases=[[[0,0],[0,0],[0,0]],[[1,0],[0,0],[0,0]],
        [[0,1],[1,0],[0,0]],[[1,1],[2,1],[0,1]]];
    print!("\"gamma_row_cases\":[");
    for (case,e) in row_cases.iter().enumerate(){
        let mut score=0;
        for gamma in 1..P{
            let noise=pow(gamma,28);let inv=pow(noise,P-2);
            let row=e.map(|v|add(v[0],mul(gamma,v[1])));
            let mut best_inactive=0;
            for inactive in 0..P{
                let mut s=0;
                for kappa in 1..P{
                    let delta=add(inactive,add(mul(kappa,row[0]),
                        add(mul(pow(kappa,2),row[1]),mul(pow(kappa,3),row[2]))));
                    // Scaling all residuals, final coefficients and compact
                    // errors bijects strategies for nonzero noise factors.
                    s+=best[mul(delta,inv)];
                }
                best_inactive=best_inactive.max(s);
            }
            score+=best_inactive;
        }
        if case>0{print!(",")}
        print!("{{\"case\":{case},\"numerator\":{score},\"denominator\":{}}}",first_den*((P-1)*(P-1)) as u64);
    }
    println!("],");
    let nonzero_finals=chosen.iter().flatten().filter(|&&v|v!=(0,0)).count();
    println!("\"states_selecting_nonzero_final\":{nonzero_finals},\"query_miss_numerator\":15,\"query_miss_denominator\":28,");
    println!("\"wall_seconds\":{},",start.elapsed().as_secs_f64());
    println!("\"scope\":\"Exhaustive compact response and adaptive affine-final strategies in stated reduced game; four fixed component-row families with optimal pre-kappa inactive per gamma. No image-invalid targets, payment acceptance, or QM31 extrapolation.\"");
    println!("}}");
}
