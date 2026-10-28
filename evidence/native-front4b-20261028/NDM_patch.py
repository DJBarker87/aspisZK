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
 projections={'scalar': 'r.output_lane == NDM_native::reference_tuple(authenticated,candidate_afterstate).3 && r.checkpoint_sequence == NDM_native::reference_tuple(authenticated,candidate_afterstate).4', 'master': 'r.master_account[NDM_native::index()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).0[NDM_native::index()]', 'checkpoint': 'r.checkpoint_account[NDM_native::index()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).1[NDM_native::index()]', 'lane': 'r.selected_lane_account[NDM_native::index()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).2[NDM_native::index()]', 'anchor': 'r.historical_global_anchor[NDM_native::index8()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).5[NDM_native::index8()]', 'live_pool': 'r.lane_transition.live_snapshot.pool[NDM_native::index()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).6.pool[NDM_native::index()]', 'live_domain': 'r.lane_transition.live_snapshot.deployment_domain[NDM_native::index()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).6.deployment_domain[NDM_native::index()]', 'live_scalar': 'r.lane_transition.live_snapshot.sequence == NDM_native::reference_tuple(authenticated,candidate_afterstate).6.sequence && r.lane_transition.live_snapshot.next_pair_index == NDM_native::reference_tuple(authenticated,candidate_afterstate).6.next_pair_index', 'live_root': 'r.lane_transition.live_snapshot.current_root[NDM_native::index8()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).6.current_root[NDM_native::index8()]', 'live_frontier': 'r.lane_transition.live_snapshot.frontier[NDM_native::level()][NDM_native::index8()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).6.frontier[NDM_native::level()][NDM_native::index8()]', 'candidate_scalar': 'r.lane_transition.candidate_afterstate.next_pair_index == NDM_native::reference_tuple(authenticated,candidate_afterstate).7.next_pair_index', 'candidate_root': 'r.lane_transition.candidate_afterstate.next_root[NDM_native::index8()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).7.next_root[NDM_native::index8()]', 'candidate_frontier': 'r.lane_transition.candidate_afterstate.next_frontier[NDM_native::level()][NDM_native::index8()] == NDM_native::reference_tuple(authenticated,candidate_afterstate).7.next_frontier[NDM_native::level()][NDM_native::index8()]'}
 # Fixed index avoids unrelated nondeterministic reads in postconditions; later window checks use own proof harness.
 ens=projections.get(window,projections['scalar'])
 if os.environ.get('NDM_INVERT'):ens='!('+ens+')'
 s=b.replace('fn asq8_common(', '#[cfg_attr(kani, kani::ensures(|r| '+ens+'))]\nfn asq8_common(',1)
 s+='\n#[cfg(kani)]\n#[path="NDM_native.rs"]\nmod NDM_native;\n'
 put(n,s,b)
 for name in ['NDM_native','NDM_reference']:
  put('programs/r1-cost-probe/src/'+name+'.rs',(E/(name+'.rs.txt')).read_text())
 (E/'NDM_native.patch').write_text(''.join(patch));return out
if __name__=='__main__':files()
