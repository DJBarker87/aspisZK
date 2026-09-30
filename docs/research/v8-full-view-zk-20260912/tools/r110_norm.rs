//! Private canonical base/complex arithmetic across the existing norm batch.
//! Same line coefficients, point order, zero checks and shared inversion.
use super::*;
const P110:u32=0x7fff_ffff;
#[derive(Clone,Copy,PartialEq,Debug)]struct B(u32);
impl B {
    const ZERO:Self=Self(0);
    fn input(x:M31)->Option<Self>{if x.0<P110{Some(Self(x.0))}else{None}}
    #[inline(always)]fn reduce(x:u64)->Self{Self(M31::reduce_u64(x).0)}
    #[inline(always)]fn add(self,r:Self)->Self{let x=self.0.wrapping_add(r.0);Self(if x>=P110{x-P110}else{x})}
    #[inline(always)]fn sub(self,r:Self)->Self{let x=self.0.wrapping_add(P110).wrapping_sub(r.0);Self(if x>=P110{x-P110}else{x})}
    #[inline(always)]fn neg(self)->Self{Self::ZERO.sub(self)}
    #[inline(always)]fn half(self)->Self{Self((self.0>>1)|((self.0&1)<<30))}
    #[inline(always)]fn mul(self,r:Self)->Self{
        // Canonical products, not arbitrary integers below 2^62: a single
        // fold followed by one subtraction is canonical for this bound.
        let x=u64::from(self.0)*u64::from(r.0);let s=(x&u64::from(P110))+(x>>31);
        Self(if s>=u64::from(P110){(s-u64::from(P110))as u32}else{s as u32})
    }
    fn inv(self)->Self{Self(M31(self.0).inv().0)}
}
#[derive(Clone,Copy,PartialEq,Debug)]struct C(B,B);
impl C {
    fn input(x:CM31)->Option<Self>{Some(Self(B::input(x.a)?,B::input(x.b)?))}
    fn output(self)->CM31{CM31::new(M31(self.0.0),M31(self.1.0))}
    #[inline(always)]fn add(self,r:Self)->Self{Self(self.0.add(r.0),self.1.add(r.1))}
    #[inline(always)]fn sub(self,r:Self)->Self{Self(self.0.sub(r.0),self.1.sub(r.1))}
    #[inline(always)]fn double(self)->Self{self.add(self)}
    #[inline(always)]fn half(self)->Self{Self(self.0.half(),self.1.half())}
    #[inline(always)]fn mul_m(self,r:B)->Self{Self(self.0.mul(r),self.1.mul(r))}
    #[inline(always)]fn mul(self,r:Self)->Self {
        const PP:u64=(P110 as u64)*(P110 as u64);
        let (a,b,c,d)=(u64::from(self.0.0),u64::from(self.1.0),u64::from(r.0.0),u64::from(r.1.0));
        // PP dominates b*d; both representatives are below 2*PP < 2^63.
        Self(B::reduce((a*c).wrapping_add(PP).wrapping_sub(b*d)),B::reduce((a*d).wrapping_add(b*c)))
    }
    #[inline(always)]fn square(self)->Self {
        let a=u64::from(self.0.0);let b=u64::from(self.1.0);
        Self(B::reduce((a+b)*(a+u64::from(P110)-b)),self.0.mul(self.1).add(self.0.mul(self.1)))
    }
    #[inline(always)]fn times_r(self)->Self{Self(self.0.add(self.0).sub(self.1),self.0.add(self.1.add(self.1)))}
    #[inline(always)]fn norm(self)->B{let a=u64::from(self.0.0);let b=u64::from(self.1.0);B::reduce(a*a+b*b)}
}
struct Coeff110([C;5]);
impl Coeff110 {
    fn new([a,b,c]:[K;3])->Option<Self>{
        let a=[C::input(a.c0)?,C::input(a.c1)?];let b=[C::input(b.c0)?,C::input(b.c1)?];let c=[C::input(c.c0)?,C::input(c.c1)?];
        let norm=|x:[C;2]|x[0].square().sub(x[1].square().times_r());
        let polar=|x:[C;2],y:[C;2]|x[0].mul(y[0]).sub(x[1].mul(y[1]).times_r()).double();
        let nc=norm(c);let half=norm(b).sub(nc).half();
        Some(Self([norm(a).add(nc).add(half),half,polar(a,b),polar(a,c),polar(b,c)]))
    }
    #[inline(always)]fn four(&self,x:B,y:B,t:B)->[C;4]{
        let c=&self.0;let even=c[0].add(c[1].mul_m(t));
        let odd_x=c[2].mul_m(x);let odd_y=c[3].mul_m(y);let cross=c[4].mul_m(x.mul(y));
        let positive=even.add(odd_x);let negative=even.sub(odd_x);
        let plus=odd_y.add(cross);let minus=odd_y.sub(cross);
        [positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)]
    }
}
fn batch(xs:&[B],ys:&[B])->Result<(Vec<B>,Vec<B>),Error>{
    if xs.is_empty()||ys.is_empty()||xs.iter().chain(ys).any(|x|*x==B::ZERO){return Err(Error::Domain);}
    let mut px=Vec::with_capacity(xs.len());px.push(xs[0]);for x in &xs[1..]{px.push(px.last().unwrap().mul(*x));}
    let mut py=Vec::with_capacity(ys.len());py.push(ys[0]);for y in &ys[1..]{py.push(py.last().unwrap().mul(*y));}
    let p=*px.last().unwrap();let q=*py.last().unwrap();let total=p.mul(q).inv();let mut ix=total.mul(q);let mut iy=total.mul(p);
    let mut ox=vec![B::ZERO;xs.len()];for i in (1..xs.len()).rev(){ox[i]=px[i-1].mul(ix);ix=ix.mul(xs[i]);}ox[0]=ix;
    let mut oy=vec![B::ZERO;ys.len()];for i in (1..ys.len()).rev(){oy[i]=py[i-1].mul(iy);iy=iy.mul(ys[i]);}oy[0]=iy;
    Ok((ox,oy))
}
pub(super) fn try_norm(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31])->Option<Result<(Vec<CM31>,Vec<M31>),Error>>{
    let points=selected.points();
    if points.len()>Q||values.len()!=4*points.len()||base.len()!=2*points.len()||lines.len()!=points.len(){return Some(Err(Error::Shape));}
    if values.is_empty()||values.contains(&K::ZERO){return Some(Err(Error::Domain));}
    let coeff=Coeff110::new(abc)?;let mut norms=Vec::with_capacity(values.len());
    for (p,&t)in points.iter().zip(lines){norms.extend(coeff.four(B::input(p.x)?,B::input(p.y)?,B::input(t)?));}
    let norms_m:Vec<_>=norms.iter().map(|n|n.norm()).collect();
    let base:Option<Vec<B>>=base.iter().copied().map(B::input).collect();let base=base?;
    let (inverse,base_inverse)=match batch(&norms_m,&base){Ok(x)=>x,Err(e)=>return Some(Err(e))};
    let out=norms.into_iter().zip(inverse).map(|(n,d)|C(n.0.mul(d),n.1.neg().mul(d)).output()).collect();
    Some(Ok((out,base_inverse.into_iter().map(|x|M31(x.0)).collect())))
}
#[cfg(not(target_os="solana"))]
pub(super) fn controls(){
    let mut rng=0x110cea_918237abcdu64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;M31((rng%u64::from(P110))as u32)};
    for case in 0..65536{
        let mut x:[M31;4]=core::array::from_fn(|_|next());
        if case<256{let v=[0,1,P110-2,P110-1];let mut c=case;for i in &mut x{*i=M31(v[c%4]);c/=4;}}
        let a=CM31::new(x[0],x[1]);let b=CM31::new(x[2],x[3]);let qa=C::input(a).unwrap();let qb=C::input(b).unwrap();
        for (v,w)in [(qa.add(qb).output(),a.add(b)),(qa.sub(qb).output(),a.sub(b)),(qa.mul(qb).output(),a.mul(b)),(qa.square().output(),a.square()),(qa.mul_m(qb.0).output(),a.mul_m31(b.a))]{assert_eq!(v,w);}
        assert_eq!(M31(qa.norm().0),a.a.mul(a.a).add(a.b.mul(a.b)));
    }
    let mut zero=0;
    for at in 0..132 {let mut all=vec![B(1);132];all[at]=B::ZERO;assert_eq!(batch(&all[..88],&all[88..]),Err(Error::Domain));zero+=1;}
    for case in 0..512 {
        let all:Vec<_>=(0..132).map(|_|{let x=next();B(if x==M31::ZERO{1}else{x.0})}).collect();
        let (a,b)=batch(&all[..88],&all[88..]).unwrap();
        for (x,y)in all.iter().zip(a.iter().chain(&b)){assert_eq!(x.mul(*y),B(1));}
        if case==0{assert_eq!(batch(&[B(1)],&[B(P110-1)]),Ok((vec![B(1)],vec![B(P110-1)])));}
    }
    for raw in [P110,P110+1,u32::MAX]{assert_eq!(B::input(M31(raw)),None);}
    println!("R110_NORM arithmetic_profiles=65536 arithmetic_comparisons=393216 inversion_batches=512 zero_positions={zero} canonical_type_private=true");
}
