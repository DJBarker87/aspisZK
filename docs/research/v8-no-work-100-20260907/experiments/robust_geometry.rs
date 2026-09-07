//! Exact small-code adversarial search. Not a QM31 probability experiment.
fn choose(n:usize,q:usize)->usize{if q>n{return 0;}let mut r=1;for i in 0..q{r=r*(n-i)/(i+1);}r}
fn main(){let p=5usize;let t=5;let mut cases=0;let mut schedules=0;let mut sharp=[false;6];let mut adaptive=0;
    for encoded in 0..p.pow(t as u32){let mut x=encoded;let mut noise=[0usize;5];for v in &mut noise{*v=x%p;x/=p;}let b=noise.iter().filter(|v|**v!=0).count();let mut maximum=0;
        for c0 in 0..p{for c1 in 0..p{if c0==0&&c1==0{continue;}let d=usize::from(c1!=0);
            let matches:Vec<usize>=(0..t).filter(|i|(c0+c1*i)%p==noise[*i]).collect();let m=matches.len();assert!(m<=b+d);maximum=maximum.max(m);if m==b+d{sharp[b]=true;}
            let mut passed=0;for i in 0..t{for j in i+1..t{passed+=usize::from(matches.contains(&i)&&matches.contains(&j));schedules+=1;}}
            assert_eq!(passed,choose(m,2));assert!(passed<=choose((b+d).min(t),2));cases+=1;
        }}assert!(maximum<=b+1);adaptive+=1;
    }
    // Sharp falsifier for forgetting corrupted fibres: degree-one p=X,
    // received delta supported only at x=1. Matching set is {0,1}, not <=1.
    let noise=[0,1,0,0,0];let matching:Vec<_>=(0..5).filter(|i|*i==noise[*i]).collect();assert_eq!(matching,vec![0,1]);
    assert_eq!(choose(matching.len(),2),1);assert_eq!(choose(1,2),0);
    println!("PASS {cases} word/final pairs; {schedules} exact q2 schedules; {adaptive} adaptive maximizations");
    println!("Sharp B+d cases by B: {sharp:?}; zero-B false bound falsified by p=X, noise=[0,1,0,0,0]");
}
