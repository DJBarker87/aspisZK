//! Exact restricted-family falsification over F5. Compile with rustc -O.
//! Polynomial determinants, not random trials or QM31 probability estimates.
use std::time::Instant;
const P: u32 = 5;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Poly(Vec<u32>);
impl Poly {
    fn new(mut a: Vec<u32>) -> Self {
        for x in &mut a { *x %= P; }
        while a.last() == Some(&0) { a.pop(); }
        Self(a)
    }
    fn zero() -> Self { Self(Vec::new()) }
    fn one() -> Self { Self(vec![1]) }
    fn c(x: u32) -> Self { Self::new(vec![x]) }
    fn is_zero(&self) -> bool { self.0.is_empty() }
    fn degree(&self) -> usize { self.0.len().saturating_sub(1) }
    fn coeff(&self, i: usize) -> u32 { self.0.get(i).copied().unwrap_or(0) }
    fn add(&self, b: &Self) -> Self {
        Self::new((0..self.0.len().max(b.0.len())).map(|i|(self.coeff(i)+b.coeff(i))%P).collect())
    }
    fn neg(&self) -> Self { Self::new(self.0.iter().map(|&a|(P-a)%P).collect()) }
    fn sub(&self, b: &Self) -> Self { self.add(&b.neg()) }
    fn mul(&self, b: &Self) -> Self {
        if self.is_zero() || b.is_zero() { return Self::zero(); }
        let mut c=vec![0;self.degree()+b.degree()+1];
        for (i,&a) in self.0.iter().enumerate() { for(j,&d)in b.0.iter().enumerate(){c[i+j]=(c[i+j]+a*d)%P;} }
        Self::new(c)
    }
    fn scale(&self, c: u32) -> Self { Self::new(self.0.iter().map(|&x|x*c%P).collect()) }
    fn eval(&self, x: u32) -> u32 { self.0.iter().rev().fold(0,|a,&b|(a*x+b)%P) }
    fn derivative(&self) -> Self { Self::new((1..self.0.len()).map(|i|self.0[i]*(i as u32%P)%P).collect()) }
    fn shift(&self, n: usize) -> Self {
        if self.is_zero(){return Self::zero();}
        let mut a=vec![0;n]; a.extend(&self.0); Self(a)
    }
    fn div_rem(&self,b:&Self)->(Self,Self){
        assert!(!b.is_zero());
        let mut r=self.clone();let mut q=vec![0;self.degree()+1];
        let inv=inv(b.0[b.degree()]);
        while !r.is_zero() && r.degree()>=b.degree(){
            let j=r.degree()-b.degree();let c=r.0[r.degree()]*inv%P;
            q[j]=(q[j]+c)%P;r=r.sub(&b.scale(c).shift(j));
        }
        (Self::new(q),r)
    }
    fn exact_div(&self,b:&Self)->Self{let(q,r)=self.div_rem(b);assert!(r.is_zero(),"Bareiss nonexact division");q}
    fn multiplicity(&self,x:u32)->usize{
        assert!(!self.is_zero());let factor=Self::new(vec![(P-x)%P,1]);
        let mut a=self.clone();let mut count=0;
        while a.eval(x)==0 {a=a.exact_div(&factor);count+=1;}
        count
    }
}
fn inv(x:u32)->u32{assert_ne!(x,0);(1..P).find(|&y|x*y%P==1).unwrap()}

fn determinant(mut a:Vec<Vec<Poly>>)->Poly{
    let n=a.len();let mut previous=Poly::one();let mut negative=false;
    for k in 0..n-1 {
        let row=match(k..n).find(|&i|!a[i][k].is_zero()){Some(i)=>i,None=>return Poly::zero()};
        if row!=k{a.swap(row,k);negative=!negative;}
        let pivot=a[k][k].clone();
        for i in k+1..n {for j in k+1..n {
            a[i][j]=pivot.mul(&a[i][j]).sub(&a[i][k].mul(&a[k][j])).exact_div(&previous);
        }a[i][k]=Poly::zero();}
        previous=pivot;
    }
    let d=a[n-1][n-1].clone();if negative{d.neg()}else{d}
}
fn numeric_determinant(mut a:Vec<Vec<u32>>)->u32{
    let n=a.len();let mut result=1;
    for k in 0..n {
        let row=match(k..n).find(|&i|a[i][k]!=0){Some(i)=>i,None=>return 0};
        if row!=k{a.swap(row,k);result=(P-result)%P;}
        result=result*a[k][k]%P;let inverse=inv(a[k][k]);
        for i in k+1..n{let scale=a[i][k]*inverse%P;
            for j in k..n{a[i][j]=(a[i][j]+P-scale*a[k][j]%P)%P;}
        }
    }result
}
fn matrix(f:&[Poly])->Vec<Vec<Poly>>{
    // Columns are coefficients of X^j*f (j<3), then X^j*f' (j<4).
    assert_eq!(f.len(),5);let mut a=vec![vec![Poly::zero();7];7];
    for j in 0..3{for i in 0..5{a[i+j][j]=f[i].clone();}}
    for j in 0..4{for i in 1..5{a[i-1+j][3+j]=f[i].scale(i as u32);}}
    a
}
fn monic_quartic_square(f:&Poly)->Option<Poly>{
    if f.degree()!=4 || f.coeff(4)!=1{return None;}
    let b=f.coeff(3)*inv(2)%P;
    let c=(f.coeff(2)+P-b*b%P)*inv(2)%P;
    let v=Poly::new(vec![c,b,1]);if v.mul(&v)==*f{Some(v)}else{None}
}
fn check_kernel(a:&[Vec<Poly>],g:u32,v:&Poly){
    let mut vectors=Vec::new();
    for j in 0..2{
        let left=v.derivative().scale(P-2).shift(j);let right=v.shift(j);
        let vector:Vec<u32>=(0..3).map(|i|left.coeff(i)).chain((0..4).map(|i|right.coeff(i))).collect();
        for row in a{assert_eq!(row.iter().zip(&vector).fold(0,|s,(x,&y)|(s+x.eval(g)*y)%P),0);}
        vectors.push(vector);
    }
    // Independently exhaust the 25 possible linear combinations for rank two.
    for x in 0..P{for y in 0..P{
        let zero=(0..7).all(|i|(x*vectors[0][i]+y*vectors[1][i])%P==0);
        assert_eq!(zero,x==0&&y==0);
    }}
}
fn main(){
    let start=Instant::now();let mut families=0;let mut separable=0;
    let mut square_events=0;let mut root_mass=0;let mut maximum_squares=0;
    for b in 0..P{for c in 0..P{let v=Poly::new(vec![c,b,1]);let square=v.mul(&v);
        for code in 0..P.pow(4){
            let mut code=code;let mut w=[0;4];for x in &mut w{*x=code%P;code/=P;}
            let f:Vec<Poly>=(0..5).map(|i|Poly::new(vec![square.coeff(i),w.get(i).copied().unwrap_or(0)])).collect();
            let a=matrix(&f);let determinant=determinant(a.clone());families+=1;
            assert!(determinant.is_zero()||determinant.degree()<=7);
            let mut count=0;let mut mass=0;
            for gamma in 0..P{
                // Independent numeric elimination checks specialization of the polynomial determinant.
                let numeric=a.iter().map(|r|r.iter().map(|x|x.eval(gamma)).collect()).collect();
                assert_eq!(determinant.eval(gamma),numeric_determinant(numeric));
                let specialized=Poly::new(f.iter().map(|x|x.eval(gamma)).collect());
                if let Some(u)=monic_quartic_square(&specialized){
                    check_kernel(&a,gamma,&u);count+=1;
                    if !determinant.is_zero(){
                        let multiplicity=determinant.multiplicity(gamma);
                        assert!(multiplicity>=2);mass+=multiplicity;
                    }
                }
            }
            if !determinant.is_zero(){
                separable+=1;square_events+=count;root_mass+=mass;
                assert!(2*count<=determinant.degree());assert!(mass<=determinant.degree());
                maximum_squares=maximum_squares.max(count);
            }
        }
    }}
    assert_eq!(families,15625);
    // Missing content/primitive guard: D=(Z-1)^2*X specializes to zero,
    // although its residual R=X never becomes a square up to nonzero scalar.
    let h=Poly::new(vec![P-1,1]);assert_eq!(h.eval(1),0);
    assert_eq!(Poly::new(vec![0,1]).degree()%2,1);
    // Leading-degree guard: (Z-1)X^4+X^2+(Z-1)X becomes X^2 at Z=1.
    let drop=vec![Poly::zero(),h.clone(),Poly::one(),Poly::zero(),h];
    assert!(!determinant(matrix(&drop)).is_zero());
    assert_eq!(Poly::new(drop.iter().map(|x|x.eval(1)).collect()),Poly::new(vec![0,0,1]));
    // Without squarefreeness, every gamma can be a square and determinant is identically zero.
    let repeated=vec![Poly::new(vec![0,0,1]),Poly::zero(),Poly::new(vec![0,2]),Poly::zero(),Poly::one()];
    assert!(determinant(matrix(&repeated)).is_zero());
    for g in 0..P{assert!(monic_quartic_square(&Poly::new(repeated.iter().map(|x|x.eval(g)).collect())).is_some());}
    println!("{{\"field_prime\":5,\"restricted_families\":{families},\"nonzero_resultant_families\":{separable},\"square_specializations_nonzero_resultant\":{square_events},\"root_multiplicity_mass\":{root_mass},\"maximum_square_gammas\":{maximum_squares},\"numeric_determinant_checks\":{},\"content_guard_control\":true,\"degree_drop_control\":true,\"squarefree_guard_control\":true,\"scope\":\"all monic quadratic V and degree-at-most-3 W over F5 for R=V^2+Z*W; not all bivariate polynomials or causal verifier strategies\",\"seconds\":{:.9}}}",families*P as usize,start.elapsed().as_secs_f64());
}
