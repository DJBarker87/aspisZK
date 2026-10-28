from NCD_generate import *
p='crates/aspis-r1-cost-probe/src/verifier.rs';source=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);assert 'line_z_values.push(line_z);' in source
text='''
#[cfg(kani)] mod NCD_z_push {
use super::*;
'''
for claim in ['metadata','new_value','old_frame']:
 text+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+'fn '+claim+'(){\n'
 text+='''let raw:[u32;12]=kani::any();let mut line_z_values:Vec<M31>=raw.map(M31).into();let rows:usize=kani::any();kani::assume(rows<12);line_z_values.truncate(rows);
 let row:[u32;5]=kani::any();let line_z=M31(row[4]);let ptr=line_z_values.as_ptr();let k:usize=kani::any();kani::assume(rows==0||k<rows);
 let old=if rows>0{line_z_values[k].0}else{0};
 line_z_values.push(line_z);
'''
 text+=dict(metadata='assert!(line_z_values.len()==rows+1&&line_z_values.capacity()==12&&line_z_values.as_ptr()==ptr);',new_value='assert!(line_z_values[rows].0==row[4]);',old_frame='if rows>0{assert!(line_z_values[k].0==old);}') [claim]+'\n}\n'
text+='}\n';emit(p,text,'NCD_z')
