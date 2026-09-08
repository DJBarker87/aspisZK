//! Research Gao-style unique decoder for a punctured Laurent circle embedding.
//! See Gao, Algorithm 1 / Theorem 3.3 (Clemson RS.pdf). No FS/CU claim.
//! Generic polynomial arithmetic is checked; source-basis correctness is a
//! finite gate here, not a completed universal Rust/Lean encoder theorem.
use super::*;
type F=CM31;
type Poly=Vec<F>;
#[derive(Debug)] pub enum Failure{Shape,RepeatedPoint,Division,Degree,Radius,Subfield,Canonical,GlobalRadius}
fn trim(p:&mut Poly){while p.last()==Some(&F::ZERO){p.pop();}}
fn eval(p:&[F],x:F)->F{p.iter().rev().fold(F::ZERO,|s,&c|s.mul(x).add(c))}
fn mul(a:&[F],b:&[F])->Poly{if a.is_empty()||b.is_empty(){return vec![]}let mut r=vec![F::ZERO;a.len()+b.len()-1];
    for(i,&x)in a.iter().enumerate(){for(j,&y)in b.iter().enumerate(){r[i+j]=r[i+j].add(x.mul(y));}}trim(&mut r);r}
fn sub(a:&[F],b:&[F])->Poly{let mut r=vec![F::ZERO;a.len().max(b.len())];
    for(i,&x)in a.iter().enumerate(){r[i]=x;}for(i,&x)in b.iter().enumerate(){r[i]=r[i].sub(x);}trim(&mut r);r}
fn divrem(mut a:Poly,b:&[F])->Result<(Poly,Poly),Failure>{
    if b.is_empty(){return Err(Failure::Division)}trim(&mut a);let mut q=vec![F::ZERO;a.len().saturating_sub(b.len())+1];let inverse=b.last().unwrap().inv();
    while !a.is_empty()&&a.len()>=b.len(){let d=a.len()-b.len();let scale=a.last().unwrap().mul(inverse);q[d]=scale;
        for(j,&v)in b.iter().enumerate(){a[d+j]=a[d+j].sub(scale.mul(v));}trim(&mut a);}
    trim(&mut q);Ok((q,a))
}
pub struct Decoder{points:Vec<F>,vanishing:Poly,lagrange:Vec<Poly>,k:usize}
impl Decoder{
    pub fn new(points:Vec<F>,k:usize)->Result<Self,Failure>{
        let n=points.len();if k==0||k>n{return Err(Failure::Shape)}
        let distinct:std::collections::BTreeSet<_>=points.iter().map(|x|(x.a.0,x.b.0)).collect();if distinct.len()!=n{return Err(Failure::RepeatedPoint)}
        let mut vanishing=vec![F::ONE];for &x in &points{vanishing=mul(&vanishing,&[x.neg(),F::ONE]);}
        let mut lagrange=vec![];
        for &x in &points{let(q,r)=divrem(vanishing.clone(),&[x.neg(),F::ONE])?;if !r.is_empty(){return Err(Failure::Division)}
            let den=eval(&q,x);if den==F::ZERO{return Err(Failure::RepeatedPoint)}let inv=den.inv();
            lagrange.push(q.iter().map(|v|v.mul(inv)).collect());}
        Ok(Self{points,vanishing,lagrange,k})
    }
    pub fn decode(&self,received:&[F])->Result<(Poly,usize),Failure>{
        let n=self.points.len();if received.len()!=n{return Err(Failure::Shape)}
        let mut interpolation=vec![F::ZERO;n];for(i,&y)in received.iter().enumerate(){
            for(j,&c)in self.lagrange[i].iter().enumerate(){interpolation[j]=interpolation[j].add(c.mul(y));}}
        trim(&mut interpolation);
        let(mut r0,mut r1)=(self.vanishing.clone(),interpolation);let(mut t0,mut t1)=(vec![],vec![F::ONE]);
        let mut steps=0;
        while !r1.is_empty()&&2*(r1.len()-1)>=n+self.k{
            let(q,r)=divrem(r0,&r1)?;let t=sub(&t0,&mul(&q,&t1));r0=r1;r1=r;t0=t1;t1=t;
            steps+=1;if steps>n{return Err(Failure::Degree)}
        }
        if t1.is_empty()||t1.len()-1>(n-self.k)/2{return Err(Failure::Degree)}
        let(p,rem)=divrem(r1,&t1)?;if !rem.is_empty(){return Err(Failure::Division)}if p.len()>self.k{return Err(Failure::Degree)}
        let errors=self.points.iter().zip(received).filter(|(x,y)|eval(&p,**x)!=**y).count();
        if errors>(n-self.k)/2{return Err(Failure::Radius)}Ok((p,errors))
    }
}
pub fn controls(){
    let xs=(1..=9).map(|i|F::from_m31(M31(i))).collect::<Vec<_>>();let d=Decoder::new(xs.clone(),3).unwrap();let mut cases=0;
    for m in 0..32{let mut p=vec![F::from_m31(M31(m)),F::from_m31(M31(m%5)),F::from_m31(M31(m%3))];trim(&mut p);
        for a in 0..9{for b in a+1..9{for c in b+1..9{
            let mut y=xs.iter().map(|&x|eval(&p,x)).collect::<Vec<_>>();for i in[a,b,c]{y[i]=y[i].add(F::ONE);}
            let(g,e)=d.decode(&y).unwrap();assert_eq!(g,p);assert_eq!(e,3);cases+=1;
        }}}}
    let(z,e)=d.decode(&vec![F::ZERO;9]).unwrap();assert!(z.is_empty());assert_eq!(e,0);
    assert!(matches!(Decoder::new(vec![F::ONE,F::ONE],1),Err(Failure::RepeatedPoint)));
    println!("gao_small_exact_cases={cases} zero_case=true duplicate_points_rejected=true");
}
pub fn recover(ex:&super::query_graph::Extracted,source:&super::circle_candidate::CircleEncoder,base:&super::authenticated_c1::Decoder)
    ->Result<aspis_statement::state_only_trace::StateOnlyTraceFoundation,Failure>{
    recover_from_fibres(ex,source,base,&(0..289).collect::<Vec<_>>(),1153,16)
}
pub fn recover_near(ex:&super::query_graph::Extracted,source:&super::circle_candidate::CircleEncoder,base:&super::authenticated_c1::Decoder)
    ->Result<aspis_statement::state_only_trace::StateOnlyTraceFoundation,Failure>{
    // Fixed reproducibility coins ONLY. The probability theorem requires
    // independent uniform private draws, not this public deterministic seed.
    let mut ids=Vec::new();let mut seen=std::collections::BTreeSet::new();let mut draws=0;
    for counter in 0..4096u32{let h=hash(&[b"AV8/extractor-private-test-coins/v1",&[1;32],&counter.to_le_bytes()]);
        let id=u32::from_le_bytes(h[..4].try_into().unwrap())&((1<<18)-1);draws+=1;
        if seen.insert(id){ids.push(id);if ids.len()==513{break}}
    }
    if ids.len()!=513{return Err(Failure::Shape)}
    println!("GAO_PRIVATE_SAMPLE test_seed=1 distinct_fibres=513 draws={draws} uniform_law_claimed=false");
    recover_from_fibres(ex,source,base,&ids,2052,16535)
}
fn recover_from_fibres(ex:&super::query_graph::Extracted,source:&super::circle_candidate::CircleEncoder,base:&super::authenticated_c1::Decoder,
    ids:&[u32],n:usize,global_cap:usize)->Result<aspis_statement::state_only_trace::StateOnlyTraceFoundation,Failure>{
    let k=1025;let start=std::time::Instant::now();
    if n>4*ids.len()||n<k||base.first_position!=0{return Err(Failure::Shape)}
    let indices:Vec<usize>=ids.iter().flat_map(|&i|(0..4).map(move|s|4*i as usize+s)).take(n).collect();
    let fibres=corelib::circle_fri::selected_circle_fiber_points_shared(20,ids).map_err(|_|Failure::Shape)?;
    let points:Vec<F>=fibres.iter().flat_map(|p|[F::new(p.x,p.y),F::new(p.x,p.y.neg()),F::new(p.x.neg(),p.y.neg()),F::new(p.x.neg(),p.y)]).take(n).collect();
    // Exact finite bridge: low bit is y, remaining bits are T_1,T_2,...,T_256.
    // In z=x+i*y each product has Laurent support within [-512,512].
    for(i,&z)in points.iter().enumerate(){assert_eq!(z.mul(z.conjugate()),F::ONE);let mut factors=[M31::ONE;10];factors[0]=z.b;factors[1]=z.a;
        for j in 2..10{factors[j]=factors[j-1].mul(factors[j-1]).double().sub(M31::ONE);}
        for row in 0usize..1024{let mut v=M31::ONE;for j in 0..10{if(row>>j)&1==1{v=v.mul(factors[j]);}}
            assert_eq!(source.encode_c1_basis_value(row,indices[i]).unwrap(),v,"circle basis at index {} row {row}",indices[i]);}}
    let d=Decoder::new(points,k)?;let shifts:Vec<F>=d.points.iter().map(|z|z.pow(512)).collect();
    let fixed_fibres=corelib::circle_fri::selected_circle_fiber_points_shared(20,&(0..256).collect::<Vec<_>>()).map_err(|_|Failure::Shape)?;
    let fixed_points:Vec<F>=fixed_fibres.iter().flat_map(|p|[F::new(p.x,p.y),F::new(p.x,p.y.neg()),F::new(p.x.neg(),p.y.neg()),F::new(p.x.neg(),p.y)]).collect();
    let mut table=aspis_statement::state_only_trace::StateOnlyTraceFoundation{c1:std::array::from_fn(|_|vec![])};
    let mut all_bad=std::collections::BTreeSet::new();let mut sample_errors=Vec::new();
    for col in 0..16{
        let mut y=vec![];for i in 0..n{let pos=indices[i];let v=ex.totalized_value(pos/4,pos%4,col).map_err(|_|Failure::Shape)?;
            y.push(shifts[i].mul_m31(v));}
        let(p,errors)=d.decode(&y)?;sample_errors.push(errors);
        let mut fixed=vec![];for &point in &fixed_points{let v=eval(&p,point).mul(point.conjugate().pow(512));
            if v.b!=M31::ZERO{return Err(Failure::Subfield)}fixed.push(v.a);}
        table.c1[col]=base.solve_base(&fixed);
        let encoded=source.encode_c1_message(&table.c1[col]).map_err(|_|Failure::Shape)?;
        // Full source re-encoding prevents an ambient RS word outside the
        // actual circle image from being returned under a sample-only check.
        for i in 0..n{if eval(&p,d.points[i])!=shifts[i].mul_m31(encoded[indices[i]]){return Err(Failure::Subfield)}}
        for(i,_)in ex.leaves.iter().enumerate(){for slot in 0..4{let v=ex.totalized_value(i,slot,col).map_err(|_|Failure::Shape)?;
            if v!=encoded[4*i+slot]{all_bad.insert(i);}}}
    }
    if all_bad.len()>global_cap{return Err(Failure::GlobalRadius)}
    println!("GAO_RECOVERY sample_points={n} ambient_k={k} max_sample_errors={} basis_checks={} corrected_fibres={} per_column_sample_errors={sample_errors:?} seconds={}",(n-k)/2,n*1024,all_bad.len(),start.elapsed().as_secs_f64());
    Ok(table)
}
