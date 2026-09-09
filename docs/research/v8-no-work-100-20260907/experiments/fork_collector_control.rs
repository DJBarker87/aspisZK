// Bounded causal collector diagnostic. The included full search is frozen;
// its main is never called. This file does not execute payment or FS code.
mod control {
#![allow(dead_code)]
include!("helper_far_moment.rs");
use std::collections::BTreeMap;

trait ReceivedOracle {
    fn identity(&self) -> u64;
    fn read(&mut self, fibre: usize, slot: usize) -> Result<usize, &'static str>;
}
struct FullOracle { identity: u64, values: Word, reads: usize }
impl ReceivedOracle for FullOracle {
    fn identity(&self) -> u64 { self.identity }
    fn read(&mut self, fibre: usize, slot: usize) -> Result<usize, &'static str> {
        self.reads += 1;
        self.values.get(fibre).and_then(|row| row.get(slot)).copied().ok_or("oracle index")
    }
}
fn snapshot(oracle: &mut dyn ReceivedOracle) -> Word {
    std::array::from_fn(|f| std::array::from_fn(|s| {
        let v = oracle.read(f,s).expect("explicit full-oracle read");
        assert!(v < P); v
    }))
}
#[derive(Clone, Copy, Debug)]
struct Disclosure { prefix: u64, oracle: u64, alpha: usize, final_value: Final }
#[derive(Clone, Copy)]
enum Attempt { Abort, Final(Disclosure) }
#[derive(Debug, PartialEq)]
enum CollectError { Cap, Insufficient, Duplicate, PrefixMismatch, OracleMismatch, Noncanonical }
#[derive(Debug)]
struct Collected { q: V8, attempts: usize, aborts: usize, alphas: [usize;4], reads: usize }

fn interpolate(nodes: [usize;4], values: [usize;4]) -> [usize;4] {
    let mut answer = [0;4];
    for i in 0..4 {
        let mut polynomial = [1,0,0,0]; let mut degree = 0; let mut denominator = 1;
        for j in 0..4 { if i != j {
            denominator = mul(denominator,sub(nodes[i],nodes[j]));
            let mut next = [0;4];
            for d in 0..=degree {
                next[d] = sub(next[d],mul(nodes[j],polynomial[d]));
                next[d+1] = add(next[d+1],polynomial[d]);
            }
            polynomial = next; degree += 1;
        }}
        assert_ne!(denominator,0);
        let scale = mul(values[i],inv(denominator));
        for d in 0..4 { answer[d] = add(answer[d],mul(scale,polynomial[d])); }
    }
    for i in 0..4 { assert_eq!(eval(&answer,nodes[i]),values[i]); }
    answer
}
// No expected quotient, witness, or honest message is an input. Four disclosed
// finals determine the two cubic lanes in the actual contiguous low-two-bit
// order q[4*lane + alpha_power]. Oracle reads audit their received-word support.
fn collect(oracle: &mut dyn ReceivedOracle, prefix: u64, attempts: &[Attempt], cap: usize)
    -> Result<Collected,CollectError> {
    let mut selected = Vec::new(); let mut used = [false;P]; let mut aborts = 0;
    for (index,attempt) in attempts.iter().take(cap).enumerate() {
        let d = match attempt { Attempt::Abort => { aborts += 1; continue }, Attempt::Final(d) => *d };
        if d.prefix != prefix { return Err(CollectError::PrefixMismatch); }
        if d.oracle != oracle.identity() { return Err(CollectError::OracleMismatch); }
        if d.alpha >= P || d.final_value.iter().any(|&v|v>=P) { return Err(CollectError::Noncanonical); }
        if used[d.alpha] { return Err(CollectError::Duplicate); }
        used[d.alpha] = true; selected.push(d);
        if selected.len()==4 {
            let nodes = std::array::from_fn(|i|selected[i].alpha);
            let mut q = [0;8];
            for lane in 0..2 {
                let coefficients = interpolate(nodes,std::array::from_fn(|i|selected[i].final_value[lane]));
                q[4*lane..4*lane+4].copy_from_slice(&coefficients);
            }
            let word = snapshot(oracle);
            for d in &selected {
                assert_eq!(forward(&q,d.alpha),d.final_value);
                // Actual oracle values are available, but not assumed to agree.
                for f in 0..T { let _ = sub(f_eval(&d.final_value,points()[f]),fold(points()[f],&word[f],d.alpha)); }
            }
            return Ok(Collected { q, attempts:index+1, aborts, alphas:nodes, reads:16 });
        }
    }
    Err(if attempts.len()>cap {CollectError::Cap} else {CollectError::Insufficient})
}
fn response_polynomial(claim:usize,c0:usize,c1:usize) -> [usize;7] {
    [c0,c1,0,0,sub(mul(claim,inv(4)),c0),0,0]
}
fn image_weights(mode:usize,k:usize,tau:usize) -> V8 {
    let mut w=transpose(mode,&ordinary(k)); w[7]=add(w[7],tau);
    if mode==0 { w[6]=add(w[6],mul(2,pow(tau,2))); }
    else { w[5]=sub(w[5],mul(2,pow(tau,2))); }
    w
}
fn true_response(w:&V8,q:&V8) -> [usize;7] {
    let mut out=[0;7];
    for lane in 0..2 {
        let r=4*lane; let dual=[w[r],w[r+3],w[r+2],w[r+1]];
        for i in 0..4 { for j in 0..4 { out[i+j]=add(out[i+j],mul(inv(4),mul(dual[i],q[r+j]))); }}
    }
    assert_eq!(mul(4,add(out[0],out[4])),dot(w,q)); out
}
fn match_mask(points:&[Point;T],word:&Word,a:usize,f:&Final)->usize {
    (0..T).fold(0,|mask,i|mask | (usize::from(f_eval(f,points[i])==fold(points[i],&word[i],a))<<i))
}
fn raw_support(points:&[Point;T],word:&Word,q:&V8)->usize {
    (0..T).fold(0,|mask,f|mask | (usize::from((0..4).all(|s|encode(q,slots(points[f])[s])==word[f][s]))<<f))
}
#[derive(Clone, Debug)]
struct Audit { q:V8, coherent:usize, common:usize, raw:usize, image:[usize;2], ordinary:usize,
    combined:usize, prior_polynomial:[usize;7], all_prior_zero:bool }
fn audit(oracle:&mut dyn ReceivedOracle, mode:usize,k:usize,tau:usize,claim:usize,
    response:&[usize;7],records:&[Disclosure],q:V8) -> Audit {
    let points=points(); let word=snapshot(oracle); let w=image_weights(mode,k,tau);
    let expected=true_response(&w,&q);
    let polynomial=std::array::from_fn(|i|sub(response[i],expected[i]));
    let im=image(mode,&q); let ordinary_error=sub(claim,dot(&transpose(mode,&ordinary(k)),&q));
    let combined=sub(ordinary_error,add(mul(tau,im[0]),mul(pow(tau,2),im[1])));
    assert_eq!(mul(4,add(polynomial[0],polynomial[4])),combined);
    let (mapped,omitted)=multiply_reference(mode,&q);
    assert_eq!(dot(&transpose(mode,&ordinary(k)),&q),dot(&ordinary(k),&mapped));
    assert_eq!(im==[0,0],omitted==[0;4]);
    let mut coherent=0; let mut common=(1<<T)-1; let mut all_prior_zero=true;
    for d in records {
        let prior=sub(eval(response,d.alpha),dot(&weights(mode,k,tau,d.alpha),&d.final_value));
        if forward(&q,d.alpha)==d.final_value {
            coherent+=1; common &= match_mask(&points,&word,d.alpha,&d.final_value);
            assert_eq!(eval(&polynomial,d.alpha),prior);
            all_prior_zero &= prior==0;
        }
    }
    let raw=raw_support(&points,&word,&q);
    // Four distinct actual alpha values, same quotient: agreement on a fibre
    // then determines its four slots. Check the conclusion, do not assume it.
    if coherent>=4 { assert_eq!(common,raw); }
    if coherent>=7 && all_prior_zero { assert_eq!(polynomial,[0;7]); assert_eq!(combined,0); }
    Audit {q,coherent,common,raw,image:im,ordinary:ordinary_error,combined,
        prior_polynomial:polynomial,all_prior_zero}
}
fn record(prefix:u64,oracle:u64,alpha:usize,final_value:Final)->Disclosure {
    Disclosure {prefix,oracle,alpha,final_value}
}
fn candidate_from(oracle:&mut dyn ReceivedOracle,prefix:u64,records:&[Disclosure])->Collected {
    let attempts:Vec<_>=records.iter().copied().map(Attempt::Final).collect();
    collect(oracle,prefix,&attempts,4).expect("four distinct causal disclosures")
}
fn emit_audit(label:&str,a:&Audit) {
    println!("{{\"audit\":\"{}\",\"q\":{:?},\"coherent_alpha_count\":{},\"common_fibre_mask\":{},\"raw_support_mask\":{},\"image_residual\":{:?},\"ordinary_residual\":{},\"combined_residual\":{},\"prior_polynomial\":{:?},\"all_prior_zero\":{}}}",
        label,a.q,a.coherent,a.common,a.raw,a.image,a.ordinary,a.combined,a.prior_polynomial,a.all_prior_zero);
}
fn family_case(profile:usize,mode:usize,gamma:usize,inactive:usize)->(usize,usize,usize) {
    let points=points(); let k=1; let tau=1;
    let prefix=(1000+profile*100+mode*10+gamma) as u64; let identity=prefix+10_000;
    let helper=raw_helpers(&points,profile);
    let mut oracle=FullOracle {identity,values:received(&points,&helper,mode,gamma,ood_batch(gamma)),reads:0};
    let word=snapshot(&mut oracle); let claim=initial_claim(gamma,k,inactive,ood_batch(gamma));
    let mut eligible:Vec<Vec<Vec<(Final,usize)>>>=vec![vec![vec![];P];P];
    let mut final_checks=0;
    for alpha in 0..P { let w=weights(mode,k,tau,alpha);
        for fi in 0..NF {
            let f=[fi%P,fi/P]; let mask=match_mask(&points,&word,alpha,&f); final_checks+=1;
            if mask.count_ones()==2 { eligible[alpha][dot(&w,&f)].push((f,mask)); }
        }
    }
    let mut best=0; let mut responses=Vec::new();
    for c0 in 0..P { for c1 in 0..P {
        let poly=response_polynomial(claim,c0,c1);
        let score=(0..P).filter(|&a|!eligible[a][eval(&poly,a)].is_empty()).count();
        if score>best {best=score;responses.clear();}
        if score==best {responses.push(poly);}
    }}
    assert!(!responses.is_empty()); let response=responses[0];
    let mut records=Vec::new(); let mut selected_masks=Vec::new(); let mut ambiguity=0;
    for alpha in 0..P {
        let choices=&eligible[alpha][eval(&response,alpha)];
        if let Some(&(f,mask))=choices.first() {
            records.push(record(prefix,identity,alpha,f)); selected_masks.push([alpha,mask]);
            ambiguity+=usize::from(choices.len()>1);
        }
    }
    assert_eq!(records.len(),best);
    // This is exact for one deterministic policy. No exponential all-policy
    // enumeration is implied; tied final choices are handled separately below.
    let mut candidates:BTreeMap<V8,Audit>=BTreeMap::new(); let mut quadruples=0;
    for a in 0..records.len() {for b in a+1..records.len() {for c in b+1..records.len() {for d in c+1..records.len() {
        let got=candidate_from(&mut oracle,prefix,&[records[a],records[b],records[c],records[d]]);
        quadruples+=1;
        if !candidates.contains_key(&got.q) {
            let value=audit(&mut oracle,mode,k,tau,claim,&response,&records,got.q);
            candidates.insert(got.q,value);
        }
    }}}}
    let mut hist=[[0usize;5];2]; let mut seven_hist=[[0usize;5];2];
    for value in candidates.values() {
        hist[usize::from(value.image==[0,0])][value.raw.count_ones() as usize]+=1;
        if value.coherent>=7 {seven_hist[usize::from(value.image==[0,0])][value.raw.count_ones() as usize]+=1;}
    }
    let best_coherent=candidates.values().max_by_key(|v|(v.coherent,v.raw.count_ones()));
    let best_common=candidates.values().filter(|v|v.raw.count_ones()>=2).max_by_key(|v|v.coherent);
    let mut tie_best=0; let mut tie_best_image_valid=0; let mut tie_best_audit=None;
    let mut tie_best_response=None; let mut tie_best_alphas=Vec::new();
    let mut pair_checks=0; let mut tie_seven_groups=0; let mut response_seven_groups=0;
    for poly in &responses {
        let mut has_seven=false;
        for i in 0..T {for j in i+1..T {
            let pair=(1<<i)|(1<<j); let mut group=Vec::new(); pair_checks+=1;
            for alpha in 0..P {
                let choices=&eligible[alpha][eval(poly,alpha)];
                let matching:Vec<_>=choices.iter().filter(|(_,mask)|mask&pair==pair).collect();
                assert!(matching.len()<=1); // two distinct final positions determine F
                if let Some(&&(f,_))=matching.first() {group.push(record(prefix,identity,alpha,f));}
            }
            if group.len()>=4 {
                let got=candidate_from(&mut oracle,prefix,&group[..4]);
                let value=audit(&mut oracle,mode,k,tau,claim,poly,&group,got.q);
                assert_eq!(value.coherent,group.len()); assert_eq!(value.raw&pair,pair);
                if value.image==[0,0] {tie_best_image_valid=tie_best_image_valid.max(group.len());}
                if group.len()>tie_best {
                    tie_best=group.len();tie_best_audit=Some(value);tie_best_response=Some(*poly);
                    tie_best_alphas=group.iter().map(|d|d.alpha).collect();
                }
                if group.len()>=7 {tie_seven_groups+=1;has_seven=true;}
            } else {tie_best=tie_best.max(group.len());}
        }}
        response_seven_groups+=usize::from(has_seven);
    }
    // Existing exact image-distance computation is a local independent check,
    // not a collector input or an expected honest polynomial.
    let distance=image_distance(&points,&word,mode); assert_eq!(distance,3);
    assert_eq!(tie_best_image_valid,0);
    println!("{{\"case\":[{},{},{}],\"kappa\":1,\"tau\":1,\"inactive\":{},\"claim\":{},\"best_qualifying_alphas\":{},\"optimal_response_ties\":{},\"chosen_response\":{:?},\"chosen_alphas\":{:?},\"chosen_fibre_masks\":{:?},\"chosen_final_tie_alphas\":{},\"four_disclosure_subsets\":{},\"distinct_quotients\":{},\"quotient_hist_imagevalid_then_supportsize\":{:?},\"seven_hist_imagevalid_then_supportsize\":{:?},\"chosen_policy_best_coherence\":{},\"chosen_policy_best_common_two\":{},\"all_optimal_ties_best_common_two\":{},\"all_optimal_ties_imagevalid_common_two\":{},\"all_optimal_ties_seven_pair_groups\":{},\"optimal_responses_with_seven_pair_group\":{},\"pair_checks\":{},\"image_distance\":{},\"oracle_reads\":{}}}",
        profile,mode,gamma,inactive,claim,best,responses.len(),response,records.iter().map(|d|d.alpha).collect::<Vec<_>>(),selected_masks,ambiguity,quadruples,candidates.len(),hist,seven_hist,best_coherent.map_or(0,|a|a.coherent),best_common.map_or(0,|a|a.coherent),tie_best,tie_best_image_valid,tie_seven_groups,response_seven_groups,pair_checks,distance,oracle.reads);
    if let Some(value)=best_coherent {emit_audit("chosen_policy_best_coherence",value);}
    if let Some(value)=best_common {emit_audit("chosen_policy_best_common_two",value);}
    if let Some(value)=tie_best_audit {emit_audit("all_optimal_ties_best_common_two",&value);}
    let chosen_finals:Vec<_>=records.iter().map(|d|[d.alpha,d.final_value[0],d.final_value[1]]).collect();
    let chosen_priors:Vec<_>=records.iter().map(|d|sub(eval(&response,d.alpha),dot(&weights(mode,k,tau,d.alpha),&d.final_value))).collect();
    assert!(chosen_priors.iter().all(|&v|v==0));
    println!("{{\"policy_case\":[{},{},{}],\"chosen_final_records_alpha_c0_c1\":{:?},\"chosen_priors\":{:?},\"best_pair_response\":{:?},\"best_pair_alphas\":{:?}}}",
        profile,mode,gamma,chosen_finals,chosen_priors,tie_best_response.map(|v|v.to_vec()).unwrap_or_default(),tie_best_alphas);
    (final_checks,quadruples,pair_checks)
}

fn positive_control(mode:usize)->usize {
    let points=points(); let k=1; let tau=1; let prefix=9000+mode as u64; let identity=prefix+10000;
    // Producer-only fixture coefficients: never passed to collect or audit as
    // an expected trace. The collector obtains q from four disclosed finals.
    let mut hidden=[1,2,3,4,5,6,7,0]; hidden[if mode==0{6}else{5}]=0;
    assert_eq!(image(mode,&hidden),[0,0]);
    let mut oracle=FullOracle {identity,values:std::array::from_fn(|f|slots(points[f]).map(|p|encode(&hidden,p))),reads:0};
    let w=image_weights(mode,k,tau); let claim=dot(&w,&hidden); let response=true_response(&w,&hidden);
    let records:Vec<_>=(0..P).map(|alpha|record(prefix,identity,alpha,forward(&hidden,alpha))).collect();
    let got=candidate_from(&mut oracle,prefix,&records[..4]);
    let value=audit(&mut oracle,mode,k,tau,claim,&response,&records,got.q);
    assert_eq!(got.q,hidden); // post-extraction fixture assertion, not acceptance predicate
    assert_eq!((value.coherent,value.raw,value.image,value.combined),(19,15,[0,0],0));
    let mut attempts:Vec<_>=records[..4].iter().copied().map(Attempt::Final).collect();
    attempts.insert(0,Attempt::Abort);
    let with_abort=collect(&mut oracle,prefix,&attempts,5).unwrap();
    assert_eq!((with_abort.attempts,with_abort.aborts,with_abort.q),(5,1,got.q));
    assert!(matches!(collect(&mut oracle,prefix,&attempts,4),Err(CollectError::Cap)));
    assert!(matches!(collect(&mut oracle,prefix,&attempts[..3],5),Err(CollectError::Insufficient)));
    let good:Vec<_>=records[..4].iter().copied().map(Attempt::Final).collect();
    let mut duplicate=good.clone();duplicate[1]=duplicate[0];
    assert!(matches!(collect(&mut oracle,prefix,&duplicate,4),Err(CollectError::Duplicate)));
    for (kind,mut d) in [(0,records[0]),(1,records[0]),(2,records[0]),(3,records[0])] {
        match kind {0=>d.prefix+=1,1=>d.oracle+=1,2=>d.alpha=P,_=>d.final_value[0]=P};
        let mut bad=good.clone();bad[0]=Attempt::Final(d);
        let result=collect(&mut oracle,prefix,&bad,4);
        assert!(match kind {0=>matches!(result,Err(CollectError::PrefixMismatch)),1=>matches!(result,Err(CollectError::OracleMismatch)),_=>matches!(result,Err(CollectError::Noncanonical))});
    }
    println!("{{\"positive_control_mode\":{},\"all19_coherent\":true,\"all4_fibres\":true,\"image_valid\":true,\"actual_combined_relation\":true,\"collector_attempts\":{},\"collector_reads\":{},\"abort_resume_attempts\":{},\"negative_controls\":7,\"response\":{:?},\"oracle_reads\":{}}}",mode,got.attempts,got.reads,with_abort.attempts,response,oracle.reads);
    emit_audit("honest_image_valid_control",&value); 7
}
pub fn run() {
    assert_eq!(std::env::args().nth(1).as_deref(),Some("--predeclared-prefixes"));
    let started=Instant::now();
    // Fixed before this diagnostic. Inactive choices are the already recorded
    // compatible-moment policy, optimized over kappa/tau in the frozen run.
    let cases=[(0,0,1,2),(0,0,2,18),(0,1,1,3),(0,1,2,8),
        (1,0,1,13),(1,0,2,1),(1,1,1,9),(1,1,2,11)];
    let mut finals=0;let mut subsets=0;let mut pairs=0;
    for (profile,mode,gamma,inactive) in cases {
        let (f,s,p)=family_case(profile,mode,gamma,inactive);finals+=f;subsets+=s;pairs+=p;
    }
    let negatives=positive_control(0)+positive_control(1);
    assert_eq!(finals,8*19*361);assert!(subsets<=8*3876);assert!(pairs<=8*361*6);
    println!("{{\"scope\":\"exact_predeclared_prefix_collector_control\",\"field\":19,\"prefixes\":8,\"final_candidates\":{},\"four_disclosure_subsets\":{},\"tied_response_pair_checks\":{},\"negative_controls\":{},\"seconds\":{},\"access\":\"explicit full oracle, not Merkle/replay\",\"limits\":\"source-enumeration-first policy coherence exhaustive; common-two-support optimum across all response/final ties exhaustive; arbitrary-support coherence across all final ties not enumerated; no QM31 probability\"}}",finals,subsets,pairs,negatives,started.elapsed().as_secs_f64());
}
}
fn main() { control::run(); }
