from NCD_generate import *
import json
p='crates/aspis-r1-cost-probe/src/verifier.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);fragment='flat.extend_from_slice(&values);\n            line_z_values.push(line_z);';assert fragment in s
(E/'NCD_ROW_SOURCE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',fragment=fragment,rows=12,flat_capacity=60,z_capacity=12),indent=2)+'\n')
t='''
#[cfg(kani)] mod NCD_rows_12 {
use super::*;
fn carrier<const N:usize>(n:usize)->Vec<M31>{
 assert!(core::mem::size_of::<M31>()==4&&core::mem::align_of::<M31>()==4&&core::mem::offset_of!(M31,0)==0);
 let b=alloc::boxed::Box::new(kani::any::<[u32;N]>());let ptr=alloc::boxed::Box::into_raw(b) as *mut M31;
 unsafe{Vec::from_raw_parts(ptr,n,N)}
}
'''
for claim in ['metadata','flat_new','flat_old','z_new','z_old']:
 t+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+'fn '+claim+'(){\n'
 t+='''let rows:usize=kani::any();kani::assume(rows<12);let n=5*rows;
 let mut flat=carrier::<60>(n);let mut line_z_values=carrier::<12>(rows);
 let raw:[u32;5]=kani::any();let values=raw.map(M31);let line_z=values[4];
 let j:usize=kani::any();kani::assume(j<5);let k:usize=kani::any();let z:usize=kani::any();kani::assume(rows==0||(k<n&&z<rows));
 let old=if rows>0{flat[k].0}else{0};let old_z=if rows>0{line_z_values[z].0}else{0};let fp=flat.as_ptr();let zp=line_z_values.as_ptr();
 flat.extend_from_slice(&values);
 line_z_values.push(line_z);
'''
 t+=dict(metadata='assert!(flat.len()==5*(rows+1)&&line_z_values.len()==rows+1&&flat.capacity()==60&&line_z_values.capacity()==12&&flat.as_ptr()==fp&&line_z_values.as_ptr()==zp);',flat_new='assert!(flat[n+j].0==raw[j]);',flat_old='if rows>0{assert!(flat[k].0==old);}',z_new='assert!(line_z_values[rows].0==raw[4]);',z_old='if rows>0{assert!(line_z_values[z].0==old_z);}') [claim]+'\n}\n'
t+='#[kani::proof] #[kani::unwind(8)]\n'+attrs+'''fn allocation(){let flat=Vec::<M31>::with_capacity(60);let line_z_values=Vec::<M31>::with_capacity(12);assert!(flat.len()==0&&flat.capacity()==60&&line_z_values.len()==0&&line_z_values.capacity()==12);}
}
'''
emit(p,t,'NCD_rows')
