from NCD_generate import *
import json
p='crates/aspis-r1-cost-probe/src/fast_dots.rs';frozen=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);folds=[]
for i in range(8):
 s=f'limbs[{i}] += (sums[{i}] & 0x7fff_ffff) + (sums[{i}] >> 31);';assert s in frozen;folds.append(s)
(E/'NCD_FOLD_SOURCE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',fragments=folds),indent=2)+'\n')
t='''
#[cfg(kani)] mod NCD_dot_windows {
use super::*;
'''
for claim in ['decode_success_full','decode_reject_full','source_slice','decode_readonly']:
 t+='#[kani::proof] #[kani::unwind(1024)]\n'+attrs+'fn '+claim+'(){\n'
 t+='''let q:[u8;608]=kani::any();let slot:usize=kani::any();let term:usize=kani::any();kani::assume(slot<4&&term<26);
 let at=slot*120+term*4;let j:usize=kani::any();kani::assume(j<608);let old=q[j];let ptr=q.as_ptr();
 let view=&q[slot*120+term*4..slot*120+term*4+4];let bytes:[u8;4]=view.try_into().unwrap();
 let word=u32::from_le_bytes(bytes);let decoded=M31::from_le_bytes(bytes);
'''
 t+=dict(decode_success_full='if let Some(x)=decoded{assert!(x.0==word&&x.0<2147483647);}',decode_reject_full='assert!(decoded.is_none()==(word>=2147483647));',source_slice='let k:usize=kani::any();kani::assume(k<4);assert!(view.as_ptr()==unsafe{q.as_ptr().add(at)}&&view.len()==4&&bytes[k]==q[at+k]);',decode_readonly='assert!(q[j]==old&&q.as_ptr()==ptr);')[claim]+'\n}\n'
for claim in ['fold_eight_values','fold_eight_bound','fold_sum_readonly','fold_metadata']:
 t+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+'fn '+claim+'(){\n'
 t+='''let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();let n:u64=kani::any();kani::assume(n<7);for i in 0..8{kani::assume(limbs[i]<=n*10737418238);}
 let j:usize=kani::any();kani::assume(j<8);let before=limbs[j];let sum=sums[j];let lp=limbs.as_ptr();let sp=sums.as_ptr();
'''+ '\n'.join(folds)+'\n'
 t+=dict(fold_eight_values='assert!(limbs[j]==before+(sum%2147483648)+(sum/2147483648));',fold_eight_bound='assert!(limbs[j]<=(n+1)*10737418238&&limbs[j]>=before);',fold_sum_readonly='assert!(sums[j]==sum&&sums.as_ptr()==sp);',fold_metadata='assert!(limbs.len()==8&&sums.len()==8&&limbs.as_ptr()==lp&&sums.as_ptr()==sp);')[claim]+'\n}\n'
t+='}\n';emit(p,t,'NCD_dot')
