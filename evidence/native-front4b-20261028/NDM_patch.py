from pathlib import Path
import subprocess,difflib,os
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 out={};patch=[]
 def base(n):return subprocess.check_output(['git','show',REV+':'+n],text=True)
 def put(n,s,b=''):
  out[n]=s;patch.append(''.join(difflib.unified_diff(b.splitlines(True),s.splitlines(True),fromfile='a/'+n if b else '/dev/null',tofile='b/'+n)))
 n='programs/r1-cost-probe/src/lib.rs';b=base(n)
 put(n,'#![cfg_attr(kani, feature(allocator_api))]\n'+b+'\n#[cfg(kani)]\nmod NDM_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n',b)
 n='programs/r1-cost-probe/src/r1_pool_adapter.rs';b=base(n)
 window=os.environ.get('NDM_WINDOW','scalar')
 projections={'scalar': 'r.output_lane == old(NDM_native::reference::identity_ref(authenticated.selected_lane.lane_id)) && authenticated.selected_lane.lane_id == old(authenticated.selected_lane.lane_id) && r.checkpoint_sequence == old(NDM_native::reference::identity_ref(authenticated.checkpoint.checkpoint_sequence)) && authenticated.checkpoint.checkpoint_sequence == old(authenticated.checkpoint.checkpoint_sequence)', 'master': 'r.master_account[NDM_native::index()] == old(NDM_native::reference::identity_ref(authenticated.master_account[NDM_native::index()])) && authenticated.master_account[NDM_native::index()] == old(authenticated.master_account[NDM_native::index()])', 'checkpoint': 'r.checkpoint_account[NDM_native::index()] == old(NDM_native::reference::identity_ref(authenticated.checkpoint_account[NDM_native::index()])) && authenticated.checkpoint_account[NDM_native::index()] == old(authenticated.checkpoint_account[NDM_native::index()])', 'lane': 'r.selected_lane_account[NDM_native::index()] == old(NDM_native::reference::identity_ref(authenticated.selected_lane_account[NDM_native::index()])) && authenticated.selected_lane_account[NDM_native::index()] == old(authenticated.selected_lane_account[NDM_native::index()])', 'anchor': 'r.historical_global_anchor[NDM_native::index8()] == old(NDM_native::reference::identity_ref(authenticated.checkpoint.global_root[NDM_native::index8()])) && authenticated.checkpoint.global_root[NDM_native::index8()] == old(authenticated.checkpoint.global_root[NDM_native::index8()])', 'live_pool': 'r.lane_transition.live_snapshot.pool[NDM_native::index()] == old(NDM_native::reference::identity_ref((*authenticated.live_snapshot).pool[NDM_native::index()])) && (*authenticated.live_snapshot).pool[NDM_native::index()] == old((*authenticated.live_snapshot).pool[NDM_native::index()])', 'live_domain': 'r.lane_transition.live_snapshot.deployment_domain[NDM_native::index()] == old(NDM_native::reference::identity_ref((*authenticated.live_snapshot).deployment_domain[NDM_native::index()])) && (*authenticated.live_snapshot).deployment_domain[NDM_native::index()] == old((*authenticated.live_snapshot).deployment_domain[NDM_native::index()])', 'live_scalar': 'r.lane_transition.live_snapshot.sequence == old(NDM_native::reference::identity_ref((*authenticated.live_snapshot).sequence)) && (*authenticated.live_snapshot).sequence == old((*authenticated.live_snapshot).sequence) && r.lane_transition.live_snapshot.next_pair_index == old(NDM_native::reference::identity_ref((*authenticated.live_snapshot).next_pair_index)) && (*authenticated.live_snapshot).next_pair_index == old((*authenticated.live_snapshot).next_pair_index)', 'live_root': 'r.lane_transition.live_snapshot.current_root[NDM_native::index8()] == old(NDM_native::reference::identity_ref((*authenticated.live_snapshot).current_root[NDM_native::index8()])) && (*authenticated.live_snapshot).current_root[NDM_native::index8()] == old((*authenticated.live_snapshot).current_root[NDM_native::index8()])', 'live_frontier': 'r.lane_transition.live_snapshot.frontier[NDM_native::level()][NDM_native::index8()] == old(NDM_native::reference::identity_ref((*authenticated.live_snapshot).frontier[NDM_native::level()][NDM_native::index8()])) && (*authenticated.live_snapshot).frontier[NDM_native::level()][NDM_native::index8()] == old((*authenticated.live_snapshot).frontier[NDM_native::level()][NDM_native::index8()])', 'candidate_scalar': 'r.lane_transition.candidate_afterstate.next_pair_index == old(NDM_native::reference::identity_ref((*candidate_afterstate).next_pair_index)) && (*candidate_afterstate).next_pair_index == old((*candidate_afterstate).next_pair_index)', 'candidate_root': 'r.lane_transition.candidate_afterstate.next_root[NDM_native::index8()] == old(NDM_native::reference::identity_ref((*candidate_afterstate).next_root[NDM_native::index8()])) && (*candidate_afterstate).next_root[NDM_native::index8()] == old((*candidate_afterstate).next_root[NDM_native::index8()])', 'candidate_frontier': 'r.lane_transition.candidate_afterstate.next_frontier[NDM_native::level()][NDM_native::index8()] == old(NDM_native::reference::identity_ref((*candidate_afterstate).next_frontier[NDM_native::level()][NDM_native::index8()])) && (*candidate_afterstate).next_frontier[NDM_native::level()][NDM_native::index8()] == old((*candidate_afterstate).next_frontier[NDM_native::level()][NDM_native::index8()])', 'lane_scalar': 'r.output_lane == old(NDM_native::reference::identity_ref(authenticated.selected_lane.lane_id)) && authenticated.selected_lane.lane_id == old(authenticated.selected_lane.lane_id)', 'sequence_scalar': 'r.checkpoint_sequence == old(NDM_native::reference::identity_ref(authenticated.checkpoint.checkpoint_sequence)) && authenticated.checkpoint.checkpoint_sequence == old(authenticated.checkpoint.checkpoint_sequence)', 'candidate_frontier_value': 'r.lane_transition.candidate_afterstate.next_frontier[NDM_native::level()][NDM_native::index8()] == old(NDM_native::reference::identity_ref((*candidate_afterstate).next_frontier[NDM_native::level()][NDM_native::index8()]))', 'candidate_frontier_frame': '(*candidate_afterstate).next_frontier[NDM_native::level()][NDM_native::index8()] == old((*candidate_afterstate).next_frontier[NDM_native::level()][NDM_native::index8()])'}
 # Fixed index avoids unrelated nondeterministic reads in postconditions; later window checks use own proof harness.
 ens=projections.get(window,projections['scalar'])
 if os.environ.get('NDM_INVERT'):ens='!('+ens+')'
 s=b.replace('fn asq8_common(', '#[cfg_attr(kani, kani::ensures(|r| '+ens+'))]\nfn asq8_common(',1)
 s+='\n#[cfg(kani)]\n#[path="NDM_native.rs"]\nmod NDM_native;\n'
 if os.environ.get('NDM_FIDELITY'):
  s+='\n#[cfg(kani)]\n#[path="NDM_fidelity.rs"]\nmod NDM_fidelity;\n'
 if os.environ.get('NDM_CTOR'):
  for name,expect,kind in [('transfer_statement_box','expected_transfer',0),('withdrawal_statement_box','expected_withdrawal',1)]:
   attribute='#[cfg_attr(kani,kani::ensures(|r| NDM_ctor::post(r,old(NDM_ctor::'+expect+'(&common,&public)),'+str(kind)+')))]\n'
   attribute+='#[cfg_attr(kani,kani::modifies((&*common as *const PoolV1PairForestTerminalCommonV1).cast_mut(),&raw mut NDM_ctor::CALLS,&raw mut NDM_ctor::SEEN,&raw mut NDM_ctor::SEEN_KIND))]\n'
   s=s.replace('fn '+name+'(',attribute+'fn '+name+'(',1)
  s+='\n#[cfg(kani)]\n#[path="NDM_ctor.rs"]\nmod NDM_ctor;\n'
 put(n,s,b)
 if os.environ.get('NDM_CTOR'):
  f=(E/'NDM_ctor.rs.txt').read_text().replace('NDM_CTOR_MODE',os.environ.get('NDM_CTOR_MODE','0')).replace('cfg!(NDM_ctor_negative)','true' if os.environ.get('NDM_INVERT') else 'false')
  if os.environ.get('NDM_CTOR_OBSERVE'):
   f=f.replace('#[kani::proof_for_contract(super::transfer_statement_box)]','#[kani::proof]').replace('#[kani::proof_for_contract(super::withdrawal_statement_box)]','#[kani::proof]')
   f=f.replace('let g:u8=kani::any();','let g:u8='+os.environ.get('NDM_CTOR_GROUP','0')+';')
   f=f.replace('let _=transfer_statement_box(Box::new(common),public);','let word=expected_transfer(&common,&public);let result=transfer_statement_box(Box::new(common),public);assert!(post(&result,word,0));')
   f=f.replace('let _=withdrawal_statement_box(Box::new(common),public);','let word=expected_withdrawal(&common,&public);let result=withdrawal_statement_box(Box::new(common),public);assert!(post(&result,word,1));')
  put('programs/r1-cost-probe/src/NDM_ctor.rs',f)
 if os.environ.get('NDM_FIDELITY'):
  f=(E/'NDM_fidelity.rs.txt').read_text().replace('cfg!(NDM_invert_fidelity)','true' if os.environ.get('NDM_FIDELITY_INVERT') else 'false').replace('NDM_MODIFIES','' if os.environ.get('NDM_BAD_MODIFIES') else '&raw mut NDM_COUNTER')
  put('programs/r1-cost-probe/src/NDM_fidelity.rs',f)
 n='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';b=base(n)
 original='fn require_zero(mut remaining: &[u8]) -> ProgramResult {\n    while !remaining.is_empty() {\n        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }\n        remaining = &remaining[1..];\n    }\n    Ok(())\n}'
 instrumented=original.replace('    while !remaining.is_empty() {','    #[cfg(kani)] NDM_owned::enter(remaining);\n    while !remaining.is_empty() {').replace('        remaining = &remaining[1..];','        remaining = &remaining[1..];\n        #[cfg(kani)] NDM_owned::advance(remaining);')
 assert original in b
 s=b.replace(original,instrumented,1)+'\n#[cfg(kani)]\n#[path="NDM_owned.rs"]\nmod NDM_owned;\n'
 for name in ['key','owner']:
  law='core::ptr::eq(*r,&self.'+name+') && **r == old(self.'+name+') && self.'+name+'==old(self.'+name+')'
  if os.environ.get('NDM_INVERT'):law='!('+law+')'
  s=s.replace('    fn '+name+'(', '    #[cfg_attr(kani,kani::ensures(|r| '+law+'))]\n    fn '+name+'(',1)
 for name,field in [('data','bytes'),('data_len','length')]:
  law='!old(matches!(&self.'+field+',Err(ProgramError::AccountBorrowFailed))) || matches!(r,Err(ProgramError::AccountBorrowFailed))'
  if os.environ.get('NDM_INVERT'):law='!('+law+')'
  s=s.replace('    fn '+name+'(', '    #[cfg_attr(kani,kani::ensures(|r| '+law+'))]\n    fn '+name+'(',1)
 s+='\n#[cfg(kani)]\n#[path="NDM_getters.rs"]\nmod NDM_getters;\n'
 original_copy='                Ok(data.to_vec())'
 replacement='                #[cfg(kani)] NDM_snapshot::copy_cut(account,&data,length1,length2);\n'+original_copy
 assert original_copy in s
 s=s.replace(original_copy,replacement,1)
 s+='\n#[cfg(kani)]\n#[path="NDM_snapshot.rs"]\nmod NDM_snapshot;\n'


 put(n,s,b)
 for name in ['NDM_native','NDM_reference','NDM_owned','NDM_getters','NDM_snapshot']:
  value=(E/(name+'.rs.txt')).read_text().replace('cfg!(NDM_prefix_negative)','true' if os.environ.get('NDM_PREFIX_INVERT') else 'false')
  if name=='NDM_snapshot' and os.environ.get('NDM_SNAPSHOT_PART'):
   first=' assert_eq!(good,!cfg!(NDM_negative));'
   a=value.index(' if !data.is_empty()');z=value.index(' // Observe',a)
   if os.environ['NDM_SNAPSHOT_PART']=='descriptor':value=value[:a]+value[z:]
   elif os.environ['NDM_SNAPSHOT_PART']=='byte':value=value.replace(first,' assert!(good); kani::assume(good);',1)
   else:raise ValueError('unknown snapshot split')
  put('programs/r1-cost-probe/src/'+name+'.rs',value.replace('cfg!(NDM_negative)','true' if os.environ.get('NDM_INVERT') else 'false'))
 if not os.environ.get('NDM_CALL_PROBE'):
  path='crates/aspis-statement/src/pool_v1/pair_terminal.rs'
  put(path,base(path),base(path))
 if os.environ.get('NDM_CALL_PROBE'):
  path='crates/aspis-statement/src/pool_v1/mod.rs';original=base(path)
  put(path,original+'\n#[cfg(kani)]\npub mod NDM_call_probe;\n',original)
  value=(E/'NDM_call_probe.rs.txt').read_text().replace('cfg!(NDM_probe_negative)','true' if os.environ.get('NDM_PROBE_INVERT') else 'false')
  put('crates/aspis-statement/src/pool_v1/NDM_call_probe.rs',value)
  path='crates/aspis-statement/src/pool_v1/pair_terminal.rs';original=base(path)
  signature='pub fn decode_pool_v1_pair_verified_afterstate_v1('
  pos=original.index('{',original.index(signature))+1
  put(path,original[:pos]+'\n    #[cfg(kani)] super::NDM_call_probe::inspect(bytes);'+original[pos:],original)
  path='programs/r1-cost-probe/src/r1_pool_adapter.rs'
  current=out[path];pos=current.index('{',current.index('fn decode_lane_from_pool_release('))+1
  value=current[:pos]+'\n    #[cfg(kani)] aspis_statement::pool_v1::NDM_call_probe::inspect(bytes);'+current[pos:]
  # Replace its prior patch, retaining all earlier cfg-only harness support.
  out[path]=value
  path='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';out[path]+='\n#[cfg(kani)]\n#[path="NDM_calls.rs"]\nmod NDM_calls;\n'
  put('programs/r1-cost-probe/src/NDM_calls.rs',(E/'NDM_calls.rs.txt').read_text())
  out['programs/r1-cost-probe/src/NDM_native.rs']=out['programs/r1-cost-probe/src/NDM_native.rs'].replace('#[cfg(NDM_probe)]','#[cfg(kani)]')
  patch=[]
  for path,value in out.items():
   original=subprocess.run(['git','show',REV+':'+path],capture_output=True,text=True)
   patch.append(''.join(difflib.unified_diff((original.stdout if original.returncode==0 else '').splitlines(True),value.splitlines(True),fromfile='a/'+path if original.returncode==0 else '/dev/null',tofile='b/'+path)))
 if os.environ.get('NDM_ARBITRARY'):
  from NDM_arbitrary import additions
  for path,value in additions().items():
   old=subprocess.run(['git','show',REV+':'+path],capture_output=True,text=True)
   put(path,value,old.stdout if old.returncode==0 else '')
 (E/'NDM_native.patch').write_text(''.join(patch));return out
if __name__=='__main__':files()
