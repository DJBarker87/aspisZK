use aspis_core::field::{M31,CM31,QM31};
const MOD:u64=2147483647;
fn m(a:u32,b:u32)->u32{((u64::from(a)*u64::from(b))%MOD)as u32}
fn a(x:u32,y:u32)->u32{((u64::from(x)+u64::from(y))%MOD)as u32}
fn d(x:u32,y:u32)->u32{((u64::from(x)+MOD-u64::from(y))%MOD)as u32}
fn cw(x:CM31)->[u32;2]{[x.a.0,x.b.0]}
fn qw(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn c(x:[u32;2])->CM31{CM31{a:M31(x[0]),b:M31(x[1])}}
fn q(x:[u32;4])->QM31{QM31{c0:c([x[0],x[1]]),c1:c([x[2],x[3]])}}
fn ca(x:[u32;2],y:[u32;2])->[u32;2]{[a(x[0],y[0]),a(x[1],y[1])]}
fn cd(x:[u32;2],y:[u32;2])->[u32;2]{[d(x[0],y[0]),d(x[1],y[1])]}
fn cm(x:[u32;2],y:[u32;2])->[u32;2]{let t=m(x[0],y[0]);let u=m(x[1],y[1]);
 let cross=(((u64::from(x[0])+u64::from(x[1]))*(u64::from(y[0])+u64::from(y[1])))%MOD)as u32;
 [d(t,u),d(d(cross,t),u)]}
fn cr(x:[u32;2])->[u32;2]{[d(a(x[0],x[0]),x[1]),a(x[0],a(x[1],x[1]))]}
fn qa(x:[u32;4],y:[u32;4])->[u32;4]{core::array::from_fn(|i|a(x[i],y[i]))}
fn qd(x:[u32;4],y:[u32;4])->[u32;4]{core::array::from_fn(|i|d(x[i],y[i]))}
fn qm(x:[u32;4],y:[u32;4])->[u32;4]{let x0=[x[0],x[1]];let x1=[x[2],x[3]];let y0=[y[0],y[1]];let y1=[y[2],y[3]];
 let t=cm(x0,y0);let u=cm(x1,y1);let v=cm(ca(x0,x1),ca(y0,y1));let lo=ca(t,cr(u));let hi=cd(cd(v,t),u);[lo[0],lo[1],hi[0],hi[1]]}
fn domain<const N:usize>(x:[u32;N]){for i in 0..N{assert!(u64::from(x[i])<MOD,"LPh field stub domain");}}
fn chosen<const N:usize>(value:[u32;N])->[u32;N]{let out:[u32;N]=kani::any();for i in 0..N{kani::assume(out[i]==value[i]);kani::assume(u64::from(out[i])<MOD);}out}
pub static mut NDE_LEFT:QM31=QM31::ZERO;
pub static mut NDE_RIGHT:QM31=QM31::ZERO;
pub static mut NDE_REPLY:QM31=QM31::ZERO;
pub static mut NDE_COUNT:usize=0;
pub fn qm31(x:QM31,y:QM31)->QM31{
 domain(qw(x));domain(qw(y));let out=q(chosen(qm(qw(x),qw(y))));
 unsafe{NDE_LEFT=x;NDE_RIGHT=y;NDE_REPLY=out;NDE_COUNT=NDE_COUNT.wrapping_add(1);}
 out
}
