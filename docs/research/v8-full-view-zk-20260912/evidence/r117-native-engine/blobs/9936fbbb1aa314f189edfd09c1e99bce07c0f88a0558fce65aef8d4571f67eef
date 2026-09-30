//! Exact one-component query tail. No new messages, challenges or hints.
use super::{K,M31,WeightAccumulator,Error};
#[path="r81_canonical_basis.rs"]mod canonical;
use canonical::Q as CQ;
fn input(v:K)->Option<CQ>{CQ::from_limbs([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0])}
fn output(v:CQ)->K{
    let v=v.limbs().map(M31);
    K{c0:super::corelib::field::CM31::new(v[0],v[1]),c1:super::corelib::field::CM31::new(v[2],v[3])}
}
#[derive(Default)]
pub(super) struct Query{scales:Vec<K>,xs:Vec<M31>}
impl Query{
    pub(super) fn new()->Self{Self::default()}
    pub(super) fn inject(&mut self,claim:&mut K,values:&[K],xs:&[M31],rho:K)->Result<K,Error>{
        let (scales,inc)=match prepared(values,rho){
            Some((scales,inc))=>(scales,Some(inc)),
            None=>{
                // Retained raw behavior; no invalid input is silently reduced.
                let mut power=rho;let scales:Vec<_>=values.iter().map(|_|{let v=power;power=power.mul(rho);v}).collect();
                (scales,None)
            }
        };
        // Same add_line_m31_batch shape condition at log length eight.
        if scales.is_empty()||scales.len()!=xs.len(){return Err(Error::Shape);}
        let inc=inc.unwrap_or_else(||scales.iter().zip(values).fold(K::ZERO,|s,(&a,&b)|s.add(a.mul(b))));
        self.scales=scales;self.xs=xs.to_vec();*claim=claim.add(inc);Ok(inc)
    }
    pub(super) fn terminal(&self,alpha:[K;3],finals:[K;4])->K{
        if let (Some(prefix),Some(f))=(prefix(&self.scales,&self.xs,&alpha),convert(finals)){
            return output(CQ::dot(prefix,f));
        }
        let mut old=WeightAccumulator::empty(8);
        old.add_line_m31_batch(&self.scales,&self.xs).unwrap();
        for a in alpha{old.fold_deferred_relation_arity4(a);}
        super::corelib::field::qm31_sum_products4(old.weight_prefix::<4>(),finals)
    }
}
fn convert<const N:usize>(v:[K;N])->Option<[CQ;N]>{
    let mut out=[CQ::ZERO;N];for i in 0..N{out[i]=input(v[i])?;}Some(out)
}
#[inline(never)]
fn prepared(values:&[K],rho:K)->Option<(Vec<K>,K)>{
    if values.len()!=22{return None;}
    let rho=input(rho)?;let mut power=rho;let mut scales=Vec::with_capacity(22);
    let mut sum=canonical::Dot::new();
    for (i,&value)in values.iter().enumerate(){
        let value=input(value)?;scales.push(output(power));sum.push(power,value);
        if i+1<22{power=power.mul(rho);}
    }
    Some((scales,output(sum.finish())))
}
#[inline(never)]
fn prefix(scales:&[K],xs:&[M31],alpha:&[K])->Option<[CQ;4]>{
    if scales.len()!=22||xs.len()!=22||alpha.len()>3{return None;}
    let mut powers=[[CQ::ZERO;3];3];
    for (i,&a)in alpha.iter().enumerate(){let a=input(a)?;let a2=a.square();powers[i]=[a2.mul(a),a2,a];}
    let mut sums=canonical::LineSums::new();
    for i in 0..22{
        let mut scale=input(scales[i])?;let mut x=xs[i];
        if x.0>=canonical::P{return None;}
        for p in &powers[..alpha.len()]{
            let high=x.mul(x).double().sub(M31::ONE);let cross=x.mul(high);
            scale=scale.mul(CQ::ONE.add(CQ::dot_m31(*p,[x.0,high.0,cross.0])?));
            x=high.mul(high).double().sub(M31::ONE);
        }
        let high=x.mul(x).double().sub(M31::ONE);
        sums.push(scale,[x.0,high.0,x.mul(high).0])?;
    }
    sums.finish((2*alpha.len())as u8)
}
#[cfg(not(target_os="solana"))]
pub(super) fn controls(){
    use super::corelib::field::{CM31,P};
    let mut state=0x116afdf654132u64;
    fn m(s:&mut u64)->M31{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;M31((*s%u64::from(P))as u32)}
    fn k(s:&mut u64)->K{K{c0:CM31::new(m(s),m(s)),c1:CM31::new(m(s),m(s))}}
    let mut stages=0;let mut dense_cases=0;
    let max=CQ::from_limbs([P-1;4]).unwrap();
    for n in 0..=22{
        let mut sums=canonical::LineSums::new();let mut old=[K::ZERO;4];
        for _ in 0..n{sums.push(max,[P-1;3]).unwrap();old[0]=old[0].add(output(max));for j in 1..4{old[j]=old[j].add(output(max).mul_m31(M31(P-1)));}}
        assert_eq!(sums.finish(6).unwrap().map(output),old.map(|x|{let mut x=x;for _ in 0..6{x=x.half();}x}));
    }
    assert_eq!(output(CQ::dot_m31([max;4],[P-1;4]).unwrap()),(0..4).fold(K::ZERO,|s,_|s.add(output(max).mul_m31(M31(P-1)))));
    for case in 0..2048{
        let rho=match case%17{0=>K::ZERO,1=>K::ONE,_=>k(&mut state)};
        let mut alphas:[K;3]=core::array::from_fn(|_|k(&mut state));
        if case%19==0{alphas=[K::ZERO;3];}if case%19==1{alphas=[K::ONE;3];}
        let values:Vec<_>=(0..22).map(|_|k(&mut state)).collect();
        let xs:Vec<_>=(0..22).map(|i|if case<3{M31([0,1,P-1][case])}else if case<25&&i==case-3{M31::ZERO}else{m(&mut state)}).collect();
        let mut power=rho;let scales:Vec<_>=(0..22).map(|_|{let v=power;power=power.mul(rho);v}).collect();
        let expected=scales.iter().zip(&values).fold(K::ZERO,|s,(&a,&b)|s.add(a.mul(b)));
        let mut query=Query::new();let mut claim=k(&mut state);let old_claim=claim;
        assert_eq!(query.inject(&mut claim,&values,&xs,rho),Ok(expected));assert_eq!(claim,old_claim.add(expected));assert_eq!(query.scales,scales);
        let mut old=WeightAccumulator::empty(8);old.add_line_m31_batch(&scales,&xs).unwrap();
        for r in 0..=3{
            if r>0{old.fold_deferred_relation_arity4(alphas[r-1]);}
            assert_eq!(prefix(&scales,&xs,&alphas[..r]).unwrap().map(output),old.weight_prefix::<4>());stages+=1;
        }
        let finals=core::array::from_fn(|_|k(&mut state));
        assert_eq!(query.terminal(alphas,finals),super::corelib::field::qm31_sum_products4(old.weight_prefix::<4>(),finals));
        if case<64{
            let mut dense=WeightAccumulator::empty(8);dense.add_line_m31_batch(&scales,&xs).unwrap();
            let mut v:Vec<_>=(0..256).map(|j|dense.weight_at(j)).collect();
            for a in alphas{v=v.chunks_exact(4).map(|v|v[0].add(a.mul(v[3].add(a.mul(v[2].add(a.mul(v[1])))))).half().half()).collect();}
            assert_eq!(v,old.weight_prefix::<4>());dense_cases+=1;
        }
    }
    let mut malformed=0;
    for limb in 0..4{for bad in [P,P+1,u32::MAX]{
        let mut limbs=[M31::ZERO;4];limbs[limb]=M31(bad);
        let bad=K{c0:CM31::new(limbs[0],limbs[1]),c1:CM31::new(limbs[2],limbs[3])};
        assert!(prepared(&[K::ZERO;22],bad).is_none());malformed+=1;
        for i in 0..22{
            let mut v=[K::ZERO;22];v[i]=bad;assert!(prepared(&v,K::ZERO).is_none());
            assert!(prefix(&v,&[M31::ONE;22],&[K::ZERO;3]).is_none());malformed+=2;
        }
        for i in 0..3{let mut a=[K::ZERO;3];a[i]=bad;assert!(prefix(&[K::ZERO;22],&[M31::ONE;22],&a).is_none());malformed+=1;}
    }}
    for bad in [P,P+1,u32::MAX]{for i in 0..22{let mut xs=[M31::ONE;22];xs[i]=M31(bad);assert!(prefix(&[K::ZERO;22],&xs,&[K::ZERO;3]).is_none());malformed+=1;}}
    let mut q=Query::new();let mut claim=K::ONE;
    assert_eq!(q.inject(&mut claim,&[],&[],K::ZERO),Err(Error::Shape));
    assert_eq!(q.inject(&mut claim,&[K::ZERO],&[],K::ZERO),Err(Error::Shape));assert_eq!(claim,K::ONE);
    println!("R116_QUERY profiles=2048 intermediate_prefix_checks={stages} independent_dense={dense_cases} malformed={malformed} unchanged_injection=true rho_zero_one=true no_messages_removed=true");
}
