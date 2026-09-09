// Access/closure diagnostic only. Frozen search code is included, never run.
mod overlap {
#![allow(dead_code)]
include!("helper_far_moment.rs");
use std::collections::BTreeMap;

#[derive(Clone,Copy,Debug)]
struct Record { alpha:usize, final_value:Final, observed:usize }
#[derive(Clone)]
struct Case { key:[usize;3], inactive:usize, claim:usize, response:[usize;7], records:Vec<Record> }
#[derive(Clone,Copy,Debug,PartialEq)]
enum Failure { OracleCap, CandidateCap, RecordCap, DuplicateAlpha, Noncanonical, BadObservation, BadPrior }
trait Oracle { fn read(&mut self,f:usize,s:usize)->usize; }
struct FixedOracle { word:Word, reads:usize }
impl Oracle for FixedOracle {
    fn read(&mut self,f:usize,s:usize)->usize {self.reads+=1; self.word[f][s]}
}
// One cache is shared across every candidate for the same immutable oracle.
// This is explicit ideal oracle access, not a Merkle authentication claim.
struct Cache<'a> { oracle:&'a mut dyn Oracle, saved:[Option<[usize;4]>;T],
    max_reads:usize, reads:usize, requests:usize }
impl<'a> Cache<'a> {
    fn new(oracle:&'a mut dyn Oracle,max_reads:usize)->Self {
        Self {oracle,saved:[None;T],max_reads,reads:0,requests:0}
    }
    fn fibre(&mut self,f:usize)->Result<[usize;4],Failure> {
        self.requests+=1;
        if let Some(v)=self.saved[f] {return Ok(v)}
        if self.reads+4>self.max_reads {return Err(Failure::OracleCap)}
        let v=std::array::from_fn(|s|self.oracle.read(f,s));self.reads+=4;
        if v.iter().any(|&x|x>=P) {return Err(Failure::Noncanonical)}
        self.saved[f]=Some(v);Ok(v)
    }
}
fn numbers(line:&str,key:&str)->Vec<usize> {
    let label=format!("\"{}\":",key);let start=line.find(&label).unwrap()+label.len();
    let input=&line[start..];let end=if input.starts_with('[') {
        let mut depth=0;let mut found=None;
        for (i,c) in input.char_indices() {if c=='[' {depth+=1}if c==']' {depth-=1;if depth==0 {found=Some(i+1);break}}}
        found.unwrap()
    } else {input.find([',','}']).unwrap_or(input.len())};
    input[..end].split(|c:char|!c.is_ascii_digit()).filter(|x|!x.is_empty()).map(|x|x.parse().unwrap()).collect()
}
fn parse_log(text:&str)->Vec<Case> {
    let mut output=Vec::new();let mut pending=None;
    for line in text.lines() {
        if line.starts_with("{\"case\":") {
            pending=Some(Case {key:numbers(line,"case").try_into().unwrap(),
                inactive:numbers(line,"inactive")[0],claim:numbers(line,"claim")[0],
                response:numbers(line,"chosen_response").try_into().unwrap(),records:Vec::new()});
        }
        if line.starts_with("{\"policy_case\":") {
            let mut case=pending.take().unwrap();assert_eq!(numbers(line,"policy_case"),case.key);
            let values=numbers(line,"chosen_final_records_alpha_c0_c1");
            assert_eq!(values.len()%3,0);
            case.records=values.chunks(3).map(|v|Record {alpha:v[0],final_value:[v[1],v[2]],observed:0}).collect();
            assert!(numbers(line,"chosen_priors").iter().all(|&v|v==0));output.push(case);
        }
        // The selected matching masks are retained on the preceding case line.
        if line.starts_with("{\"case\":") {
            let masks=numbers(line,"chosen_fibre_masks");
            let case=pending.as_mut().unwrap();
            case.records=masks.chunks(2).map(|v|Record {alpha:v[0],final_value:[0,0],observed:v[1]}).collect();
        }
        // Recover masks from the corresponding case record only; no optimizer.
    }
    // A second linear log pass attaches the original observed masks. This is
    // an intentionally tiny parser for the pinned machine-readable artifact.
    let mut index=0;
    for line in text.lines().filter(|l|l.starts_with("{\"case\":")) {
        let masks=numbers(line,"chosen_fibre_masks");let case=&mut output[index];
        assert_eq!(numbers(line,"case"),case.key);
        assert_eq!(masks.len(),2*case.records.len());
        for (r,pair) in case.records.iter_mut().zip(masks.chunks(2)) {
            assert_eq!(r.alpha,pair[0]);r.observed=pair[1];
        }
        index+=1;
    }
    assert_eq!(index,8);
    assert_eq!(output.iter().map(|c|c.key).collect::<Vec<_>>(),
        vec![[0,0,1],[0,0,2],[0,1,1],[0,1,2],[1,0,1],[1,0,2],[1,1,1],[1,1,2]]);
    output
}
fn interpolate_records(r:[Record;4])->V8 {
    let mut determinant=1;
    for i in 0..4 {for j in i+1..4 {determinant=mul(determinant,sub(r[j].alpha,r[i].alpha));}}
    assert_ne!(determinant,0);
    let mut q=[0;8];
    for lane in 0..2 {
        let rows=r.iter().map(|v|vec![1,v.alpha,pow(v.alpha,2),pow(v.alpha,3),v.final_value[lane]]).collect();
        let coefficients=solve(rows,4).expect("rank-four Vandermonde matrix");
        q[4*lane..4*lane+4].copy_from_slice(&coefficients);
    }
    for v in r {assert_eq!(forward(&q,v.alpha),v.final_value)}q
}
fn validate(cache:&mut Cache<'_>,mode:usize,response:&[usize;7],records:&[Record],record_cap:usize)
    ->Result<(),Failure> {
    if records.len()>record_cap {return Err(Failure::RecordCap)}
    let points=points();let mut seen=[false;P];
    for r in records {
        if r.alpha>=P||r.final_value.iter().any(|&v|v>=P)||r.observed>=1<<T {return Err(Failure::Noncanonical)}
        if seen[r.alpha] {return Err(Failure::DuplicateAlpha)}seen[r.alpha]=true;
        if eval(response,r.alpha)!=dot(&weights(mode,1,1,r.alpha),&r.final_value) {return Err(Failure::BadPrior)}
        for f in 0..T {if r.observed>>f&1==1 {
            let values=cache.fibre(f)?;
            if f_eval(&r.final_value,points[f])!=fold(points[f],&values,r.alpha) {return Err(Failure::BadObservation)}
        }}
    }Ok(())
}
#[derive(Clone,Debug)]
struct Closure {q:V8,identified:usize,counts:[usize;T],promoted:usize,
    observed_intersection:usize,overlap_checks:usize,overlap_added:usize,image:[usize;2]}
fn close(cache:&mut Cache<'_>,mode:usize,records:&[Record],q:V8)->Result<Closure,Failure> {
    let points=points();
    // Coefficient equality is checked for EVERY disclosed final, independently
    // of oracle access and observed support. It requires no honest anchor.
    let mut known:Vec<bool>=records.iter().map(|r|forward(&q,r.alpha)==r.final_value).collect();
    let mut promoted=0;let mut counts=[0;T];let mut overlap_checks=0;let mut overlap_added=0;
    loop {
        let old_promoted=promoted;let old_known=known.clone();counts=[0;T];
        for (r,&identified) in records.iter().zip(&known) {if identified {
            for f in 0..T {if r.observed>>f&1==1 {counts[f]+=1;}}
        }}
        for f in 0..T {if counts[f]>=4 {
            // Distinct identified alphas and checked observations imply four
            // slots; verify the actual slot equality against the same cache.
            let raw=cache.fibre(f)?;
            assert_eq!(slots(points[f]).map(|p|encode(&q,p)),raw);
            promoted|=1<<f;
        }}
        for (r,identified) in records.iter().zip(&mut known) {
            let mut agreements=0;
            // Reuse a promoted fibre for any later final, even if this record
            // did not itself disclose that fibre. No new oracle read needed.
            for f in 0..T {if promoted>>f&1==1 {
                let raw=cache.fibre(f)?;
                assert_eq!(f_eval(&forward(&q,r.alpha),points[f]),fold(points[f],&raw,r.alpha));
                if f_eval(&r.final_value,points[f])==f_eval(&forward(&q,r.alpha),points[f]) {agreements+=1;}
            }}
            if agreements>1 {
                overlap_checks+=1;
                // The actual reduced final degree is1 at distinct points.
                assert_eq!(r.final_value,forward(&q,r.alpha));
                if !*identified {*identified=true;overlap_added+=1;}
            }
        }
        if old_promoted==promoted && old_known==known {break}
    }
    let mut intersection=(1<<T)-1;let mut identified=0;
    for (r,&yes) in records.iter().zip(&known) {if yes {identified+=1;intersection&=r.observed;}}
    // With all coefficients disclosed, the overlap certificate is redundant
    // for cluster membership; it is still useful to audit support transport.
    assert_eq!(overlap_added,0);
    Ok(Closure {q,identified,counts,promoted,observed_intersection:intersection,
        overlap_checks,overlap_added,image:image(mode,&q)})
}
fn full_support(cache:&mut Cache<'_>,q:&V8)->Result<usize,Failure> {
    let points=points();let mut mask=0;
    for f in 0..T {if slots(points[f]).map(|p|encode(q,p))==cache.fibre(f)? {mask|=1<<f;}}
    Ok(mask)
}
fn candidates(records:&[Record],cap:usize)->Result<(BTreeMap<V8,()> ,usize),Failure> {
    let mut all=BTreeMap::new();let mut subsets=0;
    for a in 0..records.len() {for b in a+1..records.len() {for c in b+1..records.len() {for d in c+1..records.len() {
        let q=interpolate_records([records[a],records[b],records[c],records[d]]);subsets+=1;
        if !all.contains_key(&q)&&all.len()==cap {return Err(Failure::CandidateCap)}
        all.insert(q,());
    }}}}Ok((all,subsets))
}
fn frozen_case(case:&Case)->(usize,usize) {
    let [profile,mode,gamma]=case.key;let points=points();
    assert_eq!(initial_claim(gamma,1,case.inactive,ood_batch(gamma)),case.claim);
    assert_eq!(mul(4,add(case.response[0],case.response[4])),case.claim);
    let helpers=raw_helpers(&points,profile);
    let mut oracle=FixedOracle {word:received(&points,&helpers,mode,gamma,ood_batch(gamma)),reads:0};
    let mut cache=Cache::new(&mut oracle,16);
    validate(&mut cache,mode,&case.response,&case.records,19).unwrap();
    let (all,subsets)=candidates(&case.records,4096).unwrap();
    let mut hist=[[0usize;5];2];let mut max_identified=0;let mut max_promoted=0;let mut overlap_checks=0;
    let mut support_scans=0;
    for &q in all.keys() {
        let result=close(&mut cache,mode,&case.records,q).unwrap();
        let full=full_support(&mut cache,&q).unwrap();support_scans+=1;
        // In frozen cases observations are ALL actual matching fibres. Four
        // identified branches therefore expose every raw-matching fibre.
        assert_eq!(result.promoted,full);
        hist[usize::from(result.image==[0,0])][result.promoted.count_ones() as usize]+=1;
        max_identified=max_identified.max(result.identified);max_promoted=max_promoted.max(result.promoted.count_ones());
        overlap_checks+=result.overlap_checks;
    }
    println!("{{\"frozen_case\":{:?},\"records\":{},\"subsets\":{},\"candidates\":{},\"promoted_hist_imagevalid_then_support\":{:?},\"max_identified\":{},\"max_promoted_fibres\":{},\"overlap_checks\":{},\"overlap_added\":0,\"fullsupport_scans_after_closure\":{},\"oracle_slot_reads\":{},\"cache_fibre_requests\":{},\"candidate_coefficient_payload_bytes\":{},\"candidate_cap\":4096,\"record_cap\":19,\"oracle_slot_cap\":16}}",
        case.key,case.records.len(),subsets,all.len(),hist,max_identified,max_promoted,overlap_checks,support_scans,
        cache.reads,cache.requests,all.len()*std::mem::size_of::<V8>());
    (all.len(),subsets)
}
fn carried_response(q:&V8,mode:usize)->[usize;7] {
    let mut w=transpose(mode,&ordinary(1));w[7]=add(w[7],1);
    if mode==0 {w[6]=add(w[6],2)}else{w[5]=sub(w[5],2)}
    let mut output=[0;7];
    for lane in 0..2 {let row=4*lane;let dual=[w[row],w[row+3],w[row+2],w[row+1]];
        for i in 0..4 {for j in 0..4 {output[i+j]=add(output[i+j],mul(inv(4),mul(dual[i],q[row+j])));}}
    }
    assert_eq!(mul(4,add(output[0],output[4])),dot(&w,q));output
}
fn positive_control() {
    let points=points();let mode=0;
    // Producer-only anchor. It is not an input to candidate interpolation or
    // closure. The received corruption is fixed before all alpha disclosures.
    let private_q=[1,2,3,4,5,6,0,0];assert_eq!(image(mode,&private_q),[0,0]);
    let mut word:Word=std::array::from_fn(|f|slots(points[f]).map(|p|encode(&private_q,p)));
    for s in 0..4 {word[3][s]=add(word[3][s],1);}
    let observed=[3,6,5,3,6,5,3]; // 01,12,02,01,12,02,01: no common observed fibre.
    let records:Vec<_>=(0..7).map(|alpha|Record {alpha,final_value:forward(&private_q,alpha),observed:observed[alpha]}).collect();
    let response=carried_response(&private_q,mode);
    let mut oracle=FixedOracle {word,reads:0};let mut cache=Cache::new(&mut oracle,16);
    validate(&mut cache,mode,&response,&records,19).unwrap();
    let q=interpolate_records([records[0],records[1],records[2],records[3]]);
    let result=close(&mut cache,mode,&records,q).unwrap();
    assert_eq!(result.q,private_q); // post-extraction fixture assertion only
    assert_eq!((result.identified,result.counts,result.promoted,result.observed_intersection),
        (7,[5,5,4,0],7,0));assert_eq!(result.image,[0,0]);
    let closure_reads=cache.reads;assert_eq!(closure_reads,12);
    let raw=full_support(&mut cache,&result.q).unwrap();assert_eq!(raw,7);assert_eq!(cache.reads,16);
    // Actual full matching-set intersection is3 fibres, NOT the empty
    // observed intersection. A constant corruption cannot cancel in any fold.
    for r in &records {for f in 0..T {
        assert_eq!(f_eval(&r.final_value,points[f])==fold(points[f],&word[f],r.alpha),f!=3);
    }}
    println!("{{\"positive_control\":\"fixed_one_fibre_corruption_partial_observation\",\"records\":7,\"observed_masks\":{:?},\"response\":{:?},\"identified\":{},\"observation_multiplicities\":{:?},\"observed_intersection\":{},\"promoted_mask\":{},\"actual_full_matching_intersection\":{},\"image_residual\":{:?},\"overlap_checks\":{},\"overlap_added\":{},\"closure_oracle_slot_reads\":{},\"fullsupport_lookup_total_slot_reads\":{},\"q_from_disclosures\":{:?}}}",
        observed,response,result.identified,result.counts,result.observed_intersection,result.promoted,raw,
        result.image,result.overlap_checks,result.overlap_added,closure_reads,cache.reads,result.q);
    drop(cache);
    // Explicit caps and rejected malformed observations; none are assigned
    // success probability or discarded from a claimed extractor experiment.
    let mut checks=0;
    assert!(matches!(candidates(&records,0),Err(Failure::CandidateCap)));checks+=1;
    let mut limited=Cache::new(&mut oracle,8);
    assert_eq!(validate(&mut limited,mode,&response,&records,19),Err(Failure::OracleCap));checks+=1;
    drop(limited);
    let mut fresh=Cache::new(&mut oracle,16);
    assert_eq!(validate(&mut fresh,mode,&response,&records,6),Err(Failure::RecordCap));checks+=1;
    let mut duplicate=records.clone();duplicate[1]=duplicate[0];
    assert_eq!(validate(&mut fresh,mode,&response,&duplicate,19),Err(Failure::DuplicateAlpha));checks+=1;
    let mut wrong_observed=records.clone();wrong_observed[0].observed|=8;
    assert_eq!(validate(&mut fresh,mode,&response,&wrong_observed,19),Err(Failure::BadObservation));checks+=1;
    let mut malformed=records.clone();malformed[0].final_value[0]=P;
    assert_eq!(validate(&mut fresh,mode,&response,&malformed,19),Err(Failure::Noncanonical));checks+=1;
    let mut wrong_response=response;wrong_response[0]=add(wrong_response[0],1);
    assert_eq!(validate(&mut fresh,mode,&wrong_response,&records,19),Err(Failure::BadPrior));checks+=1;
    println!("{{\"explicit_failure_controls\":{},\"outcomes\":[\"candidate_cap\",\"oracle_cap\",\"record_cap\",\"duplicate_alpha\",\"bad_observation\",\"noncanonical_final\",\"bad_prior\"]}}",checks);
}
pub fn run() {
    let arguments:Vec<_>=std::env::args().collect();assert_eq!(arguments.len(),3);
    assert_eq!(arguments[1],"--frozen-log");let start=Instant::now();
    let text=std::fs::read_to_string(&arguments[2]).unwrap();let cases=parse_log(&text);
    let mut candidate_count=0;let mut subsets=0;
    for case in &cases {let (c,s)=frozen_case(case);candidate_count+=c;subsets+=s;}
    assert_eq!((candidate_count,subsets),(2553,2665));positive_control();
    println!("{{\"mode\":\"frozen_policy_overlap_closure\",\"frozen_prefixes\":8,\"candidate_count\":{},\"subsets\":{},\"seconds\":{},\"source_search_rerun\":false,\"scope\":\"Full-oracle cached observation transport; no Merkle/replay or QM31 claim; coefficient equality precedes overlap and overlap adds no new complete-final identities\"}}",candidate_count,subsets,start.elapsed().as_secs_f64());
}
}
fn main(){overlap::run()}
