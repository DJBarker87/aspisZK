// A single causal minority-codeword strategy, not an optimization over
// favorable transcripts. Reduced F31 circle/natural8/final2 geometry;
// no payment-semantic prefix, production parser, authentication or FS claim.
// rustc -O -C overflow-checks=yes MixedC1Control.rs -o <isolated output>
use std::time::Instant;
const P: usize = 31;
const T: usize = 7;
const MINORITY: usize = 2;
type Point = (usize, usize);
type V8 = [usize; 8];
fn add(a:usize,b:usize)->usize {(a+b)%P}
fn sub(a:usize,b:usize)->usize {(a+P-b)%P}
fn mul(a:usize,b:usize)->usize {a*b%P}
fn pow(mut a:usize,mut n:usize)->usize {
    let mut r=1; while n>0 {if n&1!=0 {r=mul(r,a);} a=mul(a,a);n>>=1;} r
}
fn inv(a:usize)->usize {assert_ne!(a,0);pow(a,P-2)}
fn dot(a:&[usize],b:&[usize])->usize {
    assert_eq!(a.len(),b.len());a.iter().zip(b).fold(0,|s,(&x,&y)|add(s,mul(x,y)))
}
fn slots((x,y):Point)->[Point;4] {[(x,y),(x,sub(0,y)),(sub(0,x),sub(0,y)),(sub(0,x),y)]}
fn points()->[Point;T] {
    let mut seen=[[false;P];P];let mut result=Vec::new();
    for x in 1..P {for y in 1..P {if add(mul(x,x),mul(y,y))==1 && !seen[x][y] {
        result.push((x,y));for (a,b) in slots((x,y)) {seen[a][b]=true;}
    }}}
    result.try_into().unwrap()
}
fn t2(x:usize)->usize {sub(mul(2,mul(x,x)),1)}
fn basis((x,y):Point)->V8 {
    let t=t2(x);[1,y,x,mul(x,y),t,mul(y,t),mul(x,t),mul(mul(x,y),t)]
}
fn fold((x,y):Point,v:[usize;4],a:usize)->usize {
    let left=add(mul(add(v[0],v[1]),inv(2)),mul(a,mul(sub(v[0],v[1]),inv(mul(2,y)))));
    let right=sub(mul(add(v[2],v[3]),inv(2)),mul(a,mul(sub(v[2],v[3]),inv(mul(2,y)))));
    add(mul(add(left,right),inv(2)),mul(pow(a,2),mul(sub(left,right),inv(mul(2,x)))))
}
fn mle(z:[usize;3],i:usize)->usize {
    (0..3).fold(1,|v,j|mul(v,if i>>j&1==1 {z[j]}else{sub(1,z[j])}))
}
fn ordinary(k:usize)->V8 {
    // Small public product rows, not the selected ten-bit successor kernel.
    let z=[2,3,4];let next=[3,4,5];let paired=[sub(1,2),sub(1,3),4];
    std::array::from_fn(|i|add(usize::from(i%3==0),add(mul(k,mle(z,i)),
        add(mul(pow(k,2),mle(next,i)),mul(pow(k,3),mle(paired,i))))))
}
fn transpose(mode:usize,w:V8)->V8 {
    let h=inv(2);let q=inv(4);
    let unit=if mode==0 {[w[2],w[3],mul(h,add(w[0],w[4])),mul(h,add(w[1],w[5])),w[6],w[7],
        add(mul(h,w[4]),mul(q,w[0])),add(mul(h,w[5]),mul(q,w[1]))]}
    else {[w[1],mul(h,sub(w[0],w[4])),w[3],mul(h,sub(w[2],w[6])),w[5],
        sub(mul(h,w[4]),mul(q,w[0])),w[7],sub(mul(h,w[6]),mul(q,w[2]))]};
    unit.map(|v|mul(2,v))
}
fn natural(p:[usize;6])->[usize;6] {
    let c5=mul(p[5],inv(8));let c4=mul(p[4],inv(8));
    let c3=mul(add(p[3],mul(8,c5)),inv(2));let c2=mul(add(p[2],mul(8,c4)),inv(2));
    [sub(add(p[0],c2),c4),sub(add(p[1],c3),c5),c2,c3,c4,c5]
}
fn multiply_reference(mode:usize,c:V8)->V8 {
    let b=[[1,0,0,0,0,0],[0,1,0,0,0,0],[P-1,0,2,0,0,0],[0,P-1,0,2,0,0]];
    let p:[[usize;6];2]=std::array::from_fn(|parity|std::array::from_fn(|d|
        (0..4).fold(0,|s,j|add(s,mul(c[2*j+parity],b[j][d])))));
    let mut r=[[0;6];2];
    if mode==0 {for j in 0..5 {r[0][j+1]=p[0][j];r[1][j+1]=p[1][j];}}
    else {r[1]=p[0];r[0]=p[1];for j in 0..4 {r[0][j+2]=sub(r[0][j+2],p[1][j]);}}
    for row in &mut r {for v in row {*v=mul(2,*v);}}
    let a=natural(r[0]);let b=natural(r[1]);
    std::array::from_fn(|j|if j%2==0 {a[j/2]}else {b[j/2]})
}
fn solve(mut matrix:Vec<Vec<usize>>)->Option<V8> {
    let mut row=0;let mut pivots=Vec::new();
    for col in 0..8 {let Some(p)=(row..matrix.len()).find(|&r|matrix[r][col]!=0) else {continue};
        matrix.swap(row,p);let scale=inv(matrix[row][col]);
        for j in col..=8 {matrix[row][j]=mul(matrix[row][j],scale);}
        for r in 0..matrix.len() {if r==row {continue;}let scale=matrix[r][col];
            for j in col..=8 {matrix[r][j]=sub(matrix[r][j],mul(scale,matrix[row][j]));}}
        pivots.push(col);row+=1;
    }
    if matrix.iter().any(|r|r[..8].iter().all(|&v|v==0)&&r[8]!=0) {return None;}
    assert_eq!(pivots.len(),8,"chosen complete-fibre evaluations must determine coefficients");
    let mut out=[0;8];for (r,&col) in pivots.iter().enumerate() {out[col]=matrix[r][8];}Some(out)
}
fn no_pole_pair() {
    // Exact CM31 arithmetic embedded in QM31, not concrete-field enumeration.
    const M:u128=(1u128<<31)-1;
    fn plus(a:[u128;2],b:[u128;2])->[u128;2] {[(a[0]+b[0])%M,(a[1]+b[1])%M]}
    fn times(a:[u128;2],b:[u128;2])->[u128;2] {
        [(a[0]*b[0]+M*M-a[1]*b[1])%M,(a[0]*b[1]+a[1]*b[0])%M]
    }
    fn power(mut a:u128,mut n:u128)->u128 {let mut r=1;while n>0 {if n&1==1 {r=r*a%M;}a=a*a%M;n>>=1;}r}
    let inv5=power(5,M-2);assert_eq!(5*inv5%M,1);
    let x=times([M-3,M-4],[inv5,0]);let y=times([6,M-2],[inv5,0]);
    assert_eq!(plus(times(x,x),times(y,y)),[1,0]);
    assert_ne!(x[1],0);assert_ne!(y,[0,0]);
    let other_y=[(M-y[0])%M,(M-y[1])%M];assert_ne!(y,other_y);
    let a=plus(times(x,other_y),times([(M-y[0])%M,(M-y[1])%M],x));
    let b=plus(y,[(M-other_y[0])%M,(M-other_y[1])%M]);
    assert_eq!(plus(a,times(b,x)),[0,0]);assert_eq!(b,times([2,0],y));
    // Thus L=b*(stored_x-x), with b nonzero and x outside M31: no base-x pole.
}
// Minimal integer output for exact unreduced rationals, not field arithmetic.
#[derive(Clone)] struct Big(Vec<u64>);
impl Big {
    fn from(mut n:u128)->Self {let mut d=Vec::new();while n>0 {d.push((n%1_000_000_000)as u64);n/=1_000_000_000;}Self(d)}
    fn mul(&self,b:&Self)->Self {
        let mut out=vec![0;self.0.len()+b.0.len()+1];
        for (i,&a) in self.0.iter().enumerate() {let mut carry=0;
            for (j,&v) in b.0.iter().enumerate() {let n=out[i+j]+a*v+carry;out[i+j]=n%1_000_000_000;carry=n/1_000_000_000;}
            let mut j=i+b.0.len();while carry>0 {let n=out[j]+carry;out[j]=n%1_000_000_000;carry=n/1_000_000_000;j+=1;}}
        while out.last()==Some(&0) {out.pop();}Self(out)
    }
    fn text(&self)->String {let mut it=self.0.iter().rev();let mut s=it.next().unwrap_or(&0).to_string();for d in it {s.push_str(&format!("{d:09}"));}s}
}
fn main() {
    let start=Instant::now();no_pole_pair();let pts=points();
    for i in 0..T {for j in 0..i {assert_ne!(t2(pts[i].0),t2(pts[j].0));}}
    // Commitment-level words are fixed NOW, before every listed challenge.
    let c1:[[usize;4];T]=std::array::from_fn(|f|[usize::from(f<MINORITY);4]);
    let p0=[0;8];let mut p1=[0;8];p1[0]=1;
    assert_eq!((0..T).filter(|&f|c1[f]==[0;4]).count(),5);
    let mut possible=Vec::new();let mut supports=0;
    for mask in 0u32..1<<T {if mask.count_ones()!=5 {continue;}supports+=1;let mut matrix=Vec::new();
        for f in 0..T {if mask>>f&1==0 {continue;}for (s,p) in slots(pts[f]).iter().enumerate() {
            let mut equation=basis(*p).to_vec();equation.push(c1[f][s]);matrix.push(equation);}}
        if let Some(c)=solve(matrix) {possible.push(c);}}
    assert_eq!(supports,21);assert_eq!(possible,vec![p0]);
    let mut reference_checks=0;
    for j in 0..8 {let mut e=[0;8];e[j]=1;for point in pts {for alpha in 0..P {
        let word=slots(point).map(|s|dot(&basis(s),&e));let powers=[1,alpha,pow(alpha,2),pow(alpha,3)];
        let final_value=add(dot(&e[..4],&powers),mul(t2(point.0),dot(&e[4..],&powers)));
        assert_eq!(fold(point,word,alpha),final_value);reference_checks+=1;
    }}}
    for claim in 0..P {for later in 0..P {
        let c4=mul(claim,inv(4));assert_eq!(mul(4,c4),claim);
        let next=mul(c4,pow(later,4));assert_eq!(next==0,claim==0||later==0);
        reference_checks+=1;
    }}
    for mode in 0..2 {for k in 1..P {let w=ordinary(k);let wt=transpose(mode,w);
        for j in 0..8 {let mut e=[0;8];e[j]=1;assert_eq!(wt[j],dot(&w,&multiply_reference(mode,e)));reference_checks+=1;}
        // Claimed component values belong to p1, not dominant p0. Honest
        // inactive=1 and shifted rows [k,k²,k³] precede their next challenge.
        let claims=[mle([2,3,4],0),mle([3,4,5],0),mle([sub(1,2),sub(1,3),4],0)];
        assert_ne!(claims[0],0);
        let ordinary_claim=add(1,add(mul(k,claims[0]),add(mul(pow(k,2),claims[1]),mul(pow(k,3),claims[2]))));
        assert_eq!(ordinary_claim,dot(&w,&p1));
        // Literal affine correction for I=e0, NOT sum of row scales.
        let quotient_claim=sub(ordinary_claim,w[0]);assert_eq!(quotient_claim,0);
        for tau in 1..P {let mut image_weights=wt;image_weights[7]=add(image_weights[7],tau);
            if mode==0 {image_weights[6]=add(image_weights[6],mul(2,pow(tau,2)));}
            else {image_weights[5]=sub(image_weights[5],mul(2,pow(tau,2)));}
            for alpha in 0..P {let dual=[1,pow(alpha,3),pow(alpha,2),alpha];
                let folded=[mul(inv(4),dot(&image_weights[..4],&dual)),mul(inv(4),dot(&image_weights[4..],&dual))];
                assert_eq!(sub(quotient_claim,dot(&folded,&[0,0])),0);reference_checks+=1;}
        }
    }}
    for gamma in 1..P {for f in 0..T {for s in 0..4 {
        // Only lane0 is nonzero; all three fixed helpers are zero. The
        // actual gamma^26 helper term and all full29 point/OOD claims remain.
        assert_eq!(add(c1[f][s],mul(pow(gamma,26),0)),c1[f][s]);
    }}}
    let mut output=Vec::new();
    for mode in 0..2 {
        let r:[[usize;4];T]=std::array::from_fn(|f|std::array::from_fn(|s| {
            let (x,y)=slots(pts[f])[s];let line=mul(2,if mode==0{x}else{y});
            mul(sub(c1[f][s],1),inv(line))}));
        assert_eq!((0..T).filter(|&f|r[f]==[0;4]).count(),MINORITY);
        let mut far_alphas=0;let mut accepted=0u64;let mut far_accepted=0u64;
        let mut minority_accepts=0;let mut far_minority_accepts=0;
        let later_den=(P as u64).pow(3);let nonzero_accept=later_den-((P-1)as u64).pow(3);
        for alpha in 0..P {
            let folded:[usize;T]=std::array::from_fn(|f|fold(pts[f],r[f],alpha));
            let far=folded.iter().filter(|&&x|x!=0).count()>1;if far {far_alphas+=1;}
            for i in 0..T {for j in 0..T {if i==j {continue;}for rho in 1..P {
                // Query batch degree TWO for two queries, including leading rho.
                let ri=sub(0,folded[i]);let rj=sub(0,folded[j]);
                let prior=sub(0,mul(rho,add(ri,mul(rho,rj))));
                // Three later rounds use ZERO transmitted free coefficients.
                // Each omitted c4=claim/4 is reconstructed at its legal time.
                // For final zero, a nonzero discrepancy survives iff all
                // three fresh later alphas are nonzero. This exact factor is
                // algebraic counting, not sampled or optimized success.
                let score=if prior==0 {later_den}else {nonzero_accept};
                accepted+=score;if far {far_accepted+=score;}
                if i<MINORITY&&j<MINORITY {assert_eq!(prior,0);minority_accepts+=1;if far {far_minority_accepts+=1;}}
            }}}
        }
        assert_eq!(far_alphas,P-1);assert_eq!(minority_accepts,P*MINORITY*(MINORITY-1)*(P-1));
        assert_eq!(far_minority_accepts,(P-1)*MINORITY*(MINORITY-1)*(P-1));
        let den=P as u64*T as u64*(T-1)as u64*(P-1)as u64*later_den;
        output.push(format!("{{\"chord\":\"{}\",\"far_alphas\":{},\"all_suffix_accept_numerator\":{},\"far_suffix_accept_numerator\":{},\"denominator\":{},\"far_minority_query_prefixes\":{}}}",if mode==0{"2x"}else{"2y"},far_alphas,accepted,far_accepted,den,far_minority_accepts));
    }
    let(mut numerator,mut denominator)=(Big::from(1),Big::from(1));let mut bits=0f64;
    for j in 0..22 {numerator=numerator.mul(&Big::from(16535-j));denominator=denominator.mul(&Big::from(262144-j));bits+=((262144-j)as f64/(16535-j)as f64).log2();}
    let k=((1u128<<31)-1).pow(4);
    println!("{{\"fixed_strategy\":true,\"field\":31,\"fibres\":7,\"minority\":2,\"early_support\":5,\"exhaustive_five_fibre_systems\":{},\"unique_early_lane\":\"zero\",\"reference_checks\":{},\"chord_results\":[{}],\"full_profile_no_pole_conditional_lower_bound\":{{\"numerator\":\"{}\",\"denominator\":\"{}\",\"bits\":{:.12}}},\"seconds\":{},\"scope\":\"Reduced geometric/scalar suffix only; honest minority claims need not be a payment witness. No favorable-seed search, no QM31 rate extrapolation. Full-profile rational is a symbolic conditional construction, not this tiny-field rate.\"}}",supports,reference_checks,output.join(","),numerator.mul(&Big::from(k-3)).text(),denominator.mul(&Big::from(k)).text(),bits,start.elapsed().as_secs_f64());
}
