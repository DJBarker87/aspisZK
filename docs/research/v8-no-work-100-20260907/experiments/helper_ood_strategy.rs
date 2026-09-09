// Exact REDUCED F19 circle game: fixed C1=0, three non-polynomial helper
// words, a fresh two-mode axis chord, and both false lane-zero OOD answers1.
// The actual reciprocal gamma^(-26)/L term is never silently removed.
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
struct Tables {hist:Vec<Hist>,far:Vec<bool>,folded:Vec<[usize;T]>}
fn tables(points:&[Point;T],r:&Word)->Tables {
    let mut hist=vec![[0;P];P*NF];let mut far=vec![false;P*NF];let mut folded=Vec::new();
    for a in 0..P {let word: [usize;T]=std::array::from_fn(|f|fold(points[f],&r[f],a));folded.push(word);
        for fi in 0..NF {let f=[fi%P,fi/P];let residual:[usize;T]=std::array::from_fn(|j|sub(f_eval(&f,points[j]),word[j]));
            far[a*NF+fi]=residual.iter().filter(|&&v|v!=0).count()>1;
            for i in 0..T {for j in 0..T {if i==j{continue}for rho in 1..P {hist[a*NF+fi][mul(rho,add(residual[i],mul(rho,residual[j])))] +=1;}}}
            assert_eq!(hist[a*NF+fi].iter().map(|&n|n as u64).sum::<u64>(),QUERIES);
        }
    }Tables{hist,far,folded}
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
// Four legal final-selection modes: unrestricted; far; far with prior=0;
// and a deliberately INVALID model omitting only the reciprocal OOD term.
fn prefix_values(points:&[Point;T],correct:&Tables,omitted:&Tables,mode:usize,k:usize,tau:usize,
    direct:bool)->([[[u64;4];P];P],usize) {
    let mut out=[[[0;4];P];P];let mut checks=0;
    for a in 0..P {let w=weights(mode,k,tau,a);
        for fi in 0..NF {let f=[fi%P,fi/P];let d=dot(&w,&f);let h=&correct.hist[a*NF+fi];let ho=&omitted.hist[a*NF+fi];
            for prior in 0..P {let delta=sub(prior,d);let score=QUERIES*TAIL_NUM+(TAIL_DEN-TAIL_NUM)*h[delta] as u64;
                let invalid=QUERIES*TAIL_NUM+(TAIL_DEN-TAIL_NUM)*ho[delta] as u64;
                out[a][prior][0]=out[a][prior][0].max(score);
                if correct.far[a*NF+fi] {out[a][prior][1]=out[a][prior][1].max(score);if delta==0{out[a][prior][2]=out[a][prior][2].max(score);}}
                if omitted.far[a*NF+fi] {out[a][prior][3]=out[a][prior][3].max(invalid);}
                if direct&&fi%89==0&&prior%7==0 {assert_eq!(score,slow_score(points,correct,a,&f,prior,&w));checks+=1;}
            }
        }
    }(out,checks)
}
fn response(claim:usize,c0:usize,c1:usize,a:usize)->usize {add(add(c0,mul(c1,a)),mul(sub(mul(claim,inv(4)),c0),pow(a,4)))}
fn response_schedules()->Vec<[u8;P]> {
    (0..P*P*P).map(|n|std::array::from_fn(|a|response(n/(P*P),n/P%P,n%P,a) as u8)).collect()
}
fn best_responses(v:&[[[u64;4];P];P],schedules:&[[u8;P]])->[[u64;4];P] {
    let mut result=[[0;4];P];
    for claim in 0..P {for c0 in 0..P {for c1 in 0..P {let mut sum=[0;4];let response=&schedules[(claim*P+c0)*P+c1];
        for a in 0..P{let r=response[a] as usize;for m in 0..4{sum[m]+=v[a][r][m];}}
        for m in 0..4{result[claim][m]=result[claim][m].max(sum[m]);}
    }}}result
}
fn preflight() {
    let started=Instant::now();let p=points();let references=reference_checks(&p);let tail=tail_certificate();let mut direct=0;
    let schedules=response_schedules();let mut distance_records=Vec::new();let mut scalar_steering=0;
    let mut histogram_seconds=0.0;let mut value_seconds=0.0;let mut response_seconds=0.0;
    for profile in 0..2 {let h=raw_helpers(&p,profile);for mode in 0..2 {for gamma in [1,2,3] {
        let actual=received(&p,&h,mode,gamma,1);let no_shift=received(&p,&h,mode,gamma,0);
        let stamp=Instant::now();let good=tables(&p,&actual);let bad=tables(&p,&no_shift);histogram_seconds+=stamp.elapsed().as_secs_f64();
        let distance=image_distance(&p,&actual,mode);
        distance_records.push([profile,mode,gamma,distance]);
        for (k,tau) in [(1,1),(2,3)] {let stamp=Instant::now();let (v,c)=prefix_values(&p,&good,&bad,mode,k,tau,true);direct+=c;
            value_seconds+=stamp.elapsed().as_secs_f64();let stamp=Instant::now();let best=best_responses(&v,&schedules);response_seconds+=stamp.elapsed().as_secs_f64();
            for claim in 0..P{assert!(best[claim][0]>=best[claim][1]);assert!(best[claim][1]>=best[claim][2]);
                if best[claim][1]>best[claim][2]{scalar_steering+=1;}}
        }
    }}}
    println!("{{\"mode\":\"tiny_preflight_only\",\"field\":19,\"circle_fibres\":{:?},\"chords\":[\"2x\",\"2y\"],\"reference_checks\":{},\"direct_scalar_checks\":{},\"tail_polynomial\":{:?},\"distance_records_profile_chord_gamma\":{:?},\"states_where_unrestricted_far_beats_zero_prior_far\":{},\"histogram_seconds\":{},\"value_seconds\":{},\"response_seconds\":{},\"seconds\":{},\"scope\":\"Actual reduced circle basis, both chord transposes/image equations, fixed words and reciprocal term; complete finals but only two-free-coefficient response0 family. Ordered distinct query pairs. Tiny fixed prefixes only, not an averaged causal probability or a payment/production game.\"}}",p.map(|(x,y)|[x,y]),references,direct,tail,distance_records,scalar_steering,histogram_seconds,value_seconds,response_seconds,started.elapsed().as_secs_f64());
}
fn main(){assert_eq!(std::env::args().nth(1).as_deref(),Some("--preflight"),"only bounded preflight enabled");preflight();}
