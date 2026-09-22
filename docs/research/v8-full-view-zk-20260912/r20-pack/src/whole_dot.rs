//! One reconstruction for a whole dot, not one reconstruction per 4 terms.
use crate::canonical::{Q,P,add,reduce};
pub const MAX_TERMS:usize=4096;
#[derive(Clone,Copy)]
pub struct Dot {raw:[u64;9],total:[u64;9],pending:u8,count:usize}
fn channels(q:Q)->[u32;9]{let [a,b,c,d]=q.limbs();let x=add(a,c);let y=add(b,d);[a,b,add(a,b),c,d,add(c,d),x,y,add(x,y)]}
impl Default for Dot {fn default()->Self{Self::new()}}
impl Dot {
    pub const fn new()->Self{Self{raw:[0;9],total:[0;9],pending:0,count:0}}
    fn flush(&mut self){for j in 0..9{
        // Four canonical products: raw < 4P² < 2^64.
        // Its one-fold representative is < 5P. At most 1024 chunks.
        let part=(self.raw[j]&u64::from(P)).wrapping_add(self.raw[j]>>31);
        self.total[j]=self.total[j].wrapping_add(part);self.raw[j]=0;
    }self.pending=0;}
    pub fn push(&mut self,a:Q,b:Q)->Result<(),TooLong>{
        if self.count==MAX_TERMS{return Err(TooLong)}
        if self.pending==4{self.flush()}
        let a=channels(a);let b=channels(b);
        for j in 0..9{self.raw[j]=self.raw[j].wrapping_add(u64::from(a[j])*u64::from(b[j]));}
        self.count+=1;self.pending+=1;Ok(())
    }
    pub fn finish(mut self)->Q{
        if self.count==0{return Q::ZERO}
        let small=self.count<=4;
        if !small && self.pending!=0{self.flush()}
        let r=if small{self.raw.map(reduce)}else{self.total.map(reduce)};
        let sub=|a:u32,b:u32|if a>=b{a-b}else{a+P-b};
        let part=|j:usize|[sub(r[j],r[j+1]),sub(sub(r[j+2],r[j]),r[j+1])];
        let a=part(0);let b=part(3);let c=part(6);
        Q::from_reduced_limbs([add(a[0],sub(add(b[0],b[0]),b[1])),
            add(a[1],add(b[0],add(b[1],b[1]))),
            sub(sub(c[0],a[0]),b[0]),sub(sub(c[1],a[1]),b[1])])
    }
}
#[derive(Debug,Clone,Copy)]pub struct TooLong;
pub fn dot(a:&[Q],b:&[Q])->Option<Q>{if a.len()!=b.len()||a.len()>MAX_TERMS{return None}let mut d=Dot::new();for(&a,&b)in a.iter().zip(b){d.push(a,b).ok()?}Some(d.finish())}
