from NCB_generate import *
import json
p='crates/aspis-r1-cost-probe/src/verifier.rs';src=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
body=src.split('        for &query in &queries[start..end] {',1)[1].split('            flat.extend_from_slice(&values);',1)[0]
assert 'let u=query as usize;' in body and 'return Err(Error::Query)' in body
text=r'''
#[cfg(kani)] mod NCB_geometry_row {
 use super::*;
 static mut U:usize=0;static mut CALLS:u8=0;static mut X:u32=0;static mut Y:u32=0;static mut LX:u32=0;static mut LY:u32=0;
 fn canonical()->M31{let x:u32=kani::any();kani::assume(x<2147483647);M31(x)}
 fn point(i:domain::FibreIndex)->domain::Point<M31> {unsafe{
  assert!(CALLS==0);CALLS=1;assert!(i.get()==U&&U<262144);
  let x=canonical();let y=canonical();X=x.0;Y=y.0;domain::Point{x,y}
 }}
 fn line(i:domain::FibreIndex)->M31{unsafe{
  assert!(CALLS==1||CALLS==2);let expected=U/4*4+if CALLS==1{0}else{3};assert!(i.get()==expected&&expected<262144);
  let x=canonical();if CALLS==1{LX=x.0;}else{LY=x.0;}CALLS+=1;x
 }}
 fn mul(x:M31,y:M31)->M31{unsafe{
  assert!(CALLS==3);CALLS=4;assert!(x.0==LX&&y.0==LX);assert!(x.0<2147483647&&y.0<2147483647);
  let result:u32=kani::any();kani::assume(u64::from(result)==(u64::from(x.0)*u64::from(y.0))%2147483647);M31(result)
 }}
 fn row(query:u32)->Result<([M31;5],M31),Error>{
'''+body+r'''
  Ok((values,line_z))
 }
'''
for mode in ['reject','routing','returned','zero']:
 text+='#[kani::proof] #[kani::unwind(64)]\n'+attrs+'#[kani::stub(crate::fast_domain::fibre_point,point)]\n#[kani::stub(crate::fast_domain::line_node,line)]\n#[kani::stub(M31::mul,mul)]\nfn '+mode+'(){\n'
 text+='let query:u32=kani::any();unsafe{U=query as usize;CALLS=0;}\n'
 if mode=='reject':text+='kani::assume(query>=262144);let result=row(query);assert!(matches!(result,Err(Error::Query)));unsafe{assert!(CALLS==0);}\n'
 else:
  text+='kani::assume(query<262144);let result=row(query);unsafe{assert!(CALLS==4);}\n'
  if mode=='returned':text+='''if let Ok((values,z))=result{unsafe{assert!(values[0].0==X&&values[1].0==Y&&values[2].0==LX&&values[3].0==LY&&values[4].0==z.0);let j:usize=kani::any();kani::assume(j<5);assert!(values[j].0>0&&values[j].0<2147483647);}}\n'''
  if mode=='zero':text+='''unsafe{if X==0||Y==0||LX==0||LY==0{assert!(matches!(result,Err(Error::Query)));}}\n'''
 text+='}\n'
text+='}\n';emit(p,text,'NCB_geometry_row')
(E/'NCB_GEOMETRY_ROW_SOURCE.json').write_text(json.dumps({'source':p,'revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_window':body,'sha256':hashlib.sha256(body.encode()).hexdigest(),'limit':'one source row through the zero guard; no append/outer-loop/owned Result association','callees':['NBS_U08 fibre/line qualified windows','SAQ_GeometrySource.canonical','LPf_BaseMultiply.source']},indent=2)+'\n')
