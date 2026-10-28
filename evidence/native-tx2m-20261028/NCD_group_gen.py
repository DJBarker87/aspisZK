from NCD_generate import *
p='crates/aspis-r1-cost-probe/src/verifier.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);assert 'core::array::from_fn(|j|flat_inverse[5*i+j])' in s
text='''
#[cfg(kani)] mod NCD_group_row {
use super::*;
#[kani::proof] #[kani::unwind(512)]
'''+attrs+'''fn values(){
 let raw:[u32;60]=kani::any();let flat_inverse:Vec<M31>=raw.map(M31).into();let i:usize=kani::any();kani::assume(i<12);
 let ptr=flat_inverse.as_ptr();let k:usize=kani::any();kani::assume(k<60);let old=flat_inverse[k].0;
 let row:[M31;5]=core::array::from_fn(|j|flat_inverse[5*i+j]);
 let j:usize=kani::any();kani::assume(j<5);assert!(row[j].0==raw[5*i+j]);
 assert!(flat_inverse.as_ptr()==ptr&&flat_inverse.len()==60&&flat_inverse[k].0==old);
}
}
'''
emit(p,text,'NCD_group')
