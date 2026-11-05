from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;x=json.loads((E/'NHH_INVERSE_INPUTS.json').read_text())
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],text=True)
m=re.search(r'pub fn try_inv\(self\) -> Option<QM31>',source);a=source.index('{',m.end());i=a+1;d=1
while d:d+=(source[i]=='{')-(source[i]=='}');i+=1
orig=source[a+1:i-1]
# The op-count hook is not deployed; keep its cfg verbatim for erasure.
inst=orig.replace('self','input')
changes=[('input.c0.square()','NHH_Csquare(log,input.c0)'),('input.c1.square()','NHH_Csquare(log,input.c1)'),('mul_by_r(','aspis_core::field::mul_by_r('),('norm.inv()','NHH_Cinverse(log,norm)'),('input.c0.mul(inverse_norm)','NHH_Cproduct(log,input.c0,inverse_norm)'),('input.c1.neg().mul(inverse_norm)','NHH_Cproduct(log,input.c1.neg(),inverse_norm)')]
# mul_by_r is private: use its identical frozen four-call body in this module.
changes[2]=('mul_by_r(','NHH_rotate(')
for old,new in changes:inst=inst.replace(old,new)
erased=inst
for old,new in reversed(changes):erased=erased.replace(new,old)
assert erased.replace('input','self')==orig
m2=re.search(r'pub fn mul_by_r\(x: CM31\)',source)
if m2 is None:m2=re.search(r'fn mul_by_r\(x: CM31\)',source)
a2=source.index('{',m2.end());j=a2+1;d=1
while d:d+=(source[j]=='{')-(source[j]=='}');j+=1
rotate=source[a2+1:j-1]
s='''
#[derive(Clone,Copy)]
struct NHH_Cevent{kind:u8,a:CM31,b:CM31,out:CM31}
struct NHH_Clog{events:[NHH_Cevent;5],len:usize}
fn NHH_Ccanon(x:CM31)->bool{x.a.0<P&&x.b.0<P}
fn NHH_Cevent(log:&mut NHH_Clog,kind:u8,a:CM31,b:CM31)->CM31{
 assert!(NHH_Ccanon(a)&&NHH_Ccanon(b)&&log.len<5);
 let out=CM31{a:M31(kani::any()),b:M31(kani::any())};kani::assume(NHH_Ccanon(out));
 log.events[log.len]=NHH_Cevent{kind,a,b,out};log.len+=1;out
}
fn NHH_Csquare(log:&mut NHH_Clog,a:CM31)->CM31{NHH_Cevent(log,0,a,CM31::ZERO)}
fn NHH_Cinverse(log:&mut NHH_Clog,a:CM31)->CM31{NHH_Cevent(log,1,a,CM31::ZERO)}
fn NHH_Cproduct(log:&mut NHH_Clog,a:CM31,b:CM31)->CM31{NHH_Cevent(log,2,a,b)}
fn NHH_rotate(x:CM31)->CM31{
'''+rotate+'''
}
fn NHH_try(log:&mut NHH_Clog,input:QM31)->Option<QM31>{
'''+inst+'''
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn qm_try_log(){
 let a:[u32;4]=kani::any();kani::assume(a[0]<P&&a[1]<P&&a[2]<P&&a[3]<P);
 let input=QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}};
 let z=CM31::ZERO;let e=NHH_Cevent{kind:0,a:z,b:z,out:z};let mut log=NHH_Clog{events:[e;5],len:0};
 let out=NHH_try(&mut log,input);
 let property=if input.is_zero(){log.len==0&&out.is_none()}else{
 let aa=log.events[0].out;let bb=log.events[1].out;let inv=log.events[2].out;
 log.len==5&&log.events[0].kind==0&&log.events[0].a==input.c0&&log.events[0].b==z&&
 log.events[1].kind==0&&log.events[1].a==input.c1&&log.events[1].b==z&&
 log.events[2].kind==1&&log.events[2].a==aa.sub(NHH_rotate(bb))&&log.events[2].b==z&&
 log.events[3].kind==2&&log.events[3].a==input.c0&&log.events[3].b==inv&&
 log.events[4].kind==2&&log.events[4].a==input.c1.neg()&&log.events[4].b==inv&&
 out==Some(QM31{c0:log.events[3].out,c1:log.events[4].out})};
 check(property);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn qm_zero_none(){let out=QM31::ZERO.try_inv();check(out==None);}
#[kani::proof]
#[kani::should_panic]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn qm_zero_panic(){if !cfg!(NHH_invert){let _=QM31::ZERO.inv();}}
'''
x['crates/aspis-r1-cost-probe/src/NHH_fields.rs']+=s
(E/'NHH_fields_qinverse.rs.txt').write_text(x['crates/aspis-r1-cost-probe/src/NHH_fields.rs'])
(E/'NHH_QINVERSE_INPUTS.json').write_text(json.dumps(x));(E/'NHH_QINVERSE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()},indent=1)+'\n')
(E/'NHH_QINVERSE_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',function='QM31::try_inv',original_body_sha256=hashlib.sha256(orig.encode()).hexdigest(),instrumented_body_sha256=hashlib.sha256(inst.encode()).hexdigest(),erasure_equal=True,rotate_body_sha256=hashlib.sha256(rotate.encode()).hexdigest(),opaque_sites=['square(c0)','square(c1)','inverse(norm)','mul(c0,inverse)','mul(-c1,inverse)'],unchanged_calls=['is_zero','mul_by_r','CM31.sub','CM31.neg'],zero='actual frozen return None retained before any log event'),indent=1)+'\n')
