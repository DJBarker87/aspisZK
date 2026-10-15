//! Z5: enumeration and cached observations around Z4c's unchanged Ech rank machinery.
use super::*;
use std::collections::BTreeMap;
use std::sync::OnceLock;
static SELECTED: OnceLock<[u16; N]> = OnceLock::new();
pub(super) fn transport() -> &'static [u16; N] {
    SELECTED.get().unwrap_or(&r0::transport::ROW_TO_COEFFICIENT)
}
pub(super) fn set_transport(pi: [u16; N]) {
    SELECTED.set(pi).expect("a row-to-coefficient transport is already selected");
}
pub(super) fn is_selected() -> bool { SELECTED.get().is_some() }
const MASTER: u64 = 0x5348f0b9a87835d0;
const SEARCH_SEED: u64 = 0x5a35d16120261010;
#[derive(Clone, Debug)]
struct Candidate { tau: [usize; 5], sigma: [[usize; 4]; 5] }
impl Candidate {
    fn map(&self) -> [u16; N] {
        std::array::from_fn(|r| (0..5).map(|d| self.sigma[d][(r >> (2*self.tau[d])) & 3] << (2*d)).sum::<usize>() as u16)
    }
}
fn permutations<const D: usize>() -> Vec<[usize; D]> {
    fn visit<const D: usize>(v: &mut [usize; D], i: usize, out: &mut Vec<[usize; D]>) {
        if i == D { out.push(*v); return; }
        for j in i..D { v.swap(i,j); visit(v,i+1,out); v.swap(i,j); }
    }
    let mut out = vec![];
    visit(&mut std::array::from_fn(|i| i),0,&mut out);
    out.sort(); out
}
// Rejection sampling avoids modulo bias for every Fisher-Yates choice.
fn uniform(rng: &mut Rng, n: u64) -> usize {
    let bound = u64::MAX - u64::MAX % n;
    loop { let x = rng.next(); if x < bound { return (x % n) as usize; } }
}
fn random_perm<const D: usize>(rng: &mut Rng) -> [usize; D] {
    let mut p = std::array::from_fn(|i| i);
    for i in (1..D).rev() { p.swap(i, uniform(rng,(i+1) as u64)); }
    p
}
pub(super) fn challenge(trial: usize) -> ([QM31;10], [Point<QM31>;2], Vec<usize>) {
    let mut rng = Rng(MASTER.wrapping_add((trial as u64+1).wrapping_mul(0x9e3779b97f4a7c15)));
    let a = std::array::from_fn(|_| rng.q());
    let z = [circle(rng.q()),circle(rng.q())];
    let qs = query_sets(&mut rng).remove(0).1;
    (a,z,qs)
}
struct Tables {
    claim: Vec<Vec<M31>>,
    coefficient: Vec<Vec<M31>>,
    allowed: Vec<Vec<usize>>,
    group: [usize;16],
}
impl Tables {
    fn new(a: &[QM31;10], z: &[Point<QM31>;2], qs: &[usize]) -> Self {
        let id = std::array::from_fn(|r| r as u16);
        let (raw,_) = raw_c_with_transport(a,z,qs,&id);
        let mut allowed: Vec<Vec<usize>> = vec![];
        let group = std::array::from_fn(|c| {
            let rows: Vec<_> = (0..N).filter(|&r| r!=1023 && eligible(c,r)).collect();
            if let Some(i) = allowed.iter().position(|old| *old == rows) { i }
            else { allowed.push(rows); allowed.len()-1 }
        });
        Self { claim: raw.iter().map(|r|r[1..13].to_vec()).collect(),
            coefficient: raw.iter().map(|r|r[13..].to_vec()).collect(), allowed, group }
    }
    fn row(&self, pi: &[u16;N], r: usize) -> Vec<M31> {
        let mut v = self.claim[r].clone();
        v.extend_from_slice(&self.coefficient[usize::from(pi[r])]);
        if inactive(r) {
            for i in 0..12 { v[i] = v[i].sub(self.claim[1023][i]); }
            for i in 12..112 { v[i] = v[i].sub(self.coefficient[usize::from(pi[1023])][i-12]); }
        }
        v
    }
    fn rank(&self, pi: &[u16;N], group: usize) -> usize {
        let mut e = Ech::new(112);
        for &r in &self.allowed[group] {
            e.insert(self.row(pi,r));
            if e.rank == 112 { break; }
        }
        e.rank
    }
    fn ranks(&self, pi: &[u16;N]) -> [usize;16] {
        let gr: Vec<_> = (0..self.allowed.len()).map(|g|self.rank(pi,g)).collect();
        std::array::from_fn(|c|gr[self.group[c]])
    }
    fn audit(&self, pi: &[u16;N], a: &[QM31;10], z: &[Point<QM31>;2], qs: &[usize]) {
        let (raw,_) = raw_c_with_transport(a,z,qs,pi);
        for r in 0..N {
            let expected: Vec<_> = raw[r][1..].iter().zip(&raw[1023][1..])
                .map(|(x,d)|if inactive(r){x.sub(*d)}else{*x}).collect();
            assert_eq!(self.row(pi,r),expected);
        }
        // Original C1 loop: no caching, grouping or full-rank short circuit.
        let direct: [usize;16] = std::array::from_fn(|c| {
            let mut e=Ech::new(112);
            for r in 0..N {
                if r==1023 || !eligible(c,r) {continue;}
                e.insert(raw[r][1..].iter().zip(&raw[1023][1..])
                    .map(|(x,d)|if inactive(r){x.sub(*d)}else{*x}).collect());
            }
            e.rank
        });
        assert_eq!(self.ranks(pi),direct);
    }
}
fn arg(name: &str) -> Option<String> {
    std::env::args().collect::<Vec<_>>().windows(2).find(|x|x[0]==name).map(|x|x[1].clone())
}
fn report_full(label: &str, pi: &[u16;N], tables: &[Tables;2]) -> bool {
    let random=tables[0].ranks(pi); let consecutive=tables[1].ranks(pi);
    let pass=random.iter().chain(&consecutive).all(|&r|r==112);
    println!("Z5_RANKS label={label} random={random:?} consecutive={consecutive:?} pass={pass}");
    pass
}
pub(super) fn search() {
    let start=Instant::now();
    let (a,z,qs)=challenge(0);
    let consecutive: Vec<_>=(0..22).collect();
    let tables=[Tables::new(&a,&z,&qs),Tables::new(&a,&z,&consecutive)];
    println!("Z5_SEARCH base=600eb013878a0169cdab8f222e879cd395e3a1e2 challenge_seed={MASTER:#x} search_seed={SEARCH_SEED:#x} trial=0 alpha={a:?} circle={z:?} queries={qs:?} groups={:?}",tables[0].group);
    let id=std::array::from_fn(|r|r as u16);
    for (name,pi) in [("identity",id),("D13",r0::transport::ROW_TO_COEFFICIENT)] {
        tables[0].audit(&pi,&a,&z,&qs); tables[1].audit(&pi,&a,&z,&consecutive);
        report_full(name,&pi,&tables);
    }
    let mut audit_rng=Rng(SEARCH_SEED);
    let audit_candidate=Candidate{tau:random_perm(&mut audit_rng),sigma:std::array::from_fn(|_|random_perm(&mut audit_rng))};
    tables[0].audit(&audit_candidate.map(),&a,&z,&qs);
    tables[1].audit(&audit_candidate.map(),&a,&z,&consecutive);
    println!("Z5_AUDIT cached_rows_and_grouped_ranks_match_original=true transports=identity,D13,random_digit both_sets=true");
    if std::env::args().any(|x|x=="--preflight") {return;}
    let tau=permutations::<5>();let sigma=permutations::<4>();
    let random_count=arg("--random-count").map(|x|x.parse().unwrap()).unwrap_or(100000usize);
    assert!(random_count<=100000);
    let mut rng=Rng(SEARCH_SEED);
    let mut first: Option<(usize,Candidate)>=None;
    let mut passed=0; let mut failures=0; let mut checked=0;
    let exhaustive=std::env::args().any(|x|x=="--exhaustive");
    println!("Z5_POLICY exhaustive={exhaustive} stop_after_first_successful_stage={} all_passing_candidates_checked_on_20_z4c_vectors=true",!exhaustive);
    let mut later=Vec::new();
    for trial in 1..20 {
        let (a,z,qs)=challenge(trial);
        println!("Z5_CHALLENGE trial={trial} alpha={a:?} circle={z:?} queries={qs:?}");
        later.push([Tables::new(&a,&z,&qs),Tables::new(&a,&z,&consecutive)]);
    }
    let mut distribution=BTreeMap::<(usize,usize,usize,usize,usize),usize>::new();
    for stage in 1..=3 {
        let count=match stage {1=>tau.len(),2=>tau.len()*sigma.len(),_=>random_count};
        for index in 0..count {
            let candidate=match stage {
                1=>Candidate{tau:tau[index],sigma:[[0,1,2,3];5]},
                2=>{let mut s=[[0,1,2,3];5];s[0]=sigma[index%sigma.len()];Candidate{tau:tau[index/sigma.len()],sigma:s}},
                _=>Candidate{tau:random_perm(&mut rng),sigma:std::array::from_fn(|_|random_perm(&mut rng))},
            };
            let pi=candidate.map();
            let mut failure=None;
            // Reject on the first failing semantic column; test consecutive first.
            // Distinct semantic columns with identical source row lists share a rank.
            for (trial,tables) in std::iter::once(&tables).chain(later.iter()).enumerate() {
                for group in 0..tables[0].allowed.len() {
                    let column=tables[0].group.iter().position(|&g|g==group).unwrap();
                    for set in [1,0] {
                        let rank=tables[set].rank(&pi,group);
                        if rank<112 {failure=Some((trial,set,column,rank));break;}
                    }
                    if failure.is_some(){break;}
                }
                if failure.is_some(){break;}
            }
            checked+=1;
            if let Some((trial,set,column,rank))=failure {
                failures+=1;*distribution.entry((stage,trial,set,column,rank)).or_default()+=1;
                if failures<=20 {
                    println!("Z5_FAILURE ordinal={checked} stage={stage} index={index} tau={:?} sigma={:?} first_trial={trial} first_set={} first_column={column} first_rank={rank}",candidate.tau,candidate.sigma,if set==0{"random"}else{"consecutive"});
                    report_full(&format!("failure_{failures}"),&pi,if trial==0{&tables}else{&later[trial-1]});
                }
            } else {
                passed+=1;
                println!("Z5_PASS ordinal={checked} stage={stage} index={index} tau={:?} sigma={:?}",candidate.tau,candidate.sigma);
                for (trial,tables) in std::iter::once(&tables).chain(later.iter()).enumerate() {
                    assert!(report_full(&format!("pass_{passed}_trial_{trial}"),&pi,tables));
                }
                if first.is_none(){first=Some((checked,candidate));}
            }
            if checked%100==0 {println!("Z5_PROGRESS checked={checked} passed={passed} failures={failures} wall_seconds={:.3}",start.elapsed().as_secs_f64());}
        }
        println!("Z5_STAGE_DONE stage={stage} tested={count} cumulative_passed={passed} wall_seconds={:.3}",start.elapsed().as_secs_f64());
        if passed>0 && !exhaustive { break; }
    }
    for ((stage,trial,set,column,rank),count) in distribution {
        println!("Z5_DISTRIBUTION stage={stage} first_trial={trial} first_set={} first_column={column} rank={rank} count={count}",if set==0{"random"}else{"consecutive"});
    }
    if let Some((ordinal,candidate))=first {
        println!("Z5_FIRST ordinal={ordinal} tau={:?} sigma={:?}",candidate.tau,candidate.sigma);
        let mut values=candidate.tau.to_vec();values.extend(candidate.sigma.iter().flatten());
        std::fs::write(arg("--candidate-out").unwrap_or_else(||"first-candidate.txt".into()),values.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",")+"\n").unwrap();
    }
    println!("Z5_SEARCH_DONE checked={checked} passed={passed} failures={failures} wall_seconds={:.3}",start.elapsed().as_secs_f64());
}
pub(super) fn gate() {
    let path=arg("--candidate").expect("--candidate required");
    let v:Vec<usize>=std::fs::read_to_string(path).unwrap().trim().split(',').map(|s|s.parse().unwrap()).collect();
    assert_eq!(v.len(),25);
    let c=Candidate{tau:std::array::from_fn(|i|v[i]),sigma:std::array::from_fn(|i|std::array::from_fn(|j|v[5+4*i+j]))};
    let mut t=c.tau;t.sort();assert_eq!(t,[0,1,2,3,4]);
    for s in c.sigma {let mut s=s;s.sort();assert_eq!(s,[0,1,2,3]);}
    SELECTED.set(c.map()).unwrap();
    println!("Z5_GATE tau={:?} sigma={:?} generic_trials=20 targets=100 fourth_claim_all_lanes=true",c.tau,c.sigma);
    if !std::env::args().any(|x|x=="--preflight") {
        for trial in 0..20 {
            let (a,z,qs)=challenge(trial);
            let tables=[Tables::new(&a,&z,&qs),Tables::new(&a,&z,&(0..22).collect::<Vec<_>>())];
            for (name,pi) in [("identity",std::array::from_fn(|r|r as u16)),("D13",r0::transport::ROW_TO_COEFFICIENT)] {
                report_full(&format!("control_{name}_trial_{trial}"),&pi,&tables);
            }
        }
    }
    z4c_main();
}
