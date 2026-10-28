from pathlib import Path
import subprocess,difflib,json
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
orig=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
def files():
 d={}
 p='programs/r1-cost-probe/src/lib.rs';s=orig(p);s=s.replace('use aspis_r1_cost_probe::verifier', '#![cfg_attr(kani, feature(allocator_api))]\n#[cfg(kani)] extern crate alloc;\nuse aspis_r1_cost_probe::verifier',1)
 s+='\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCV_KMX;\n#[cfg(kani)] mod NCV_reference;\n'
 d[p]=s;d['programs/r1-cost-probe/src/NCV_reference.rs']=(E/'NCV_reference.rs').read_text()
 p='programs/r1-cost-probe/src/r1_pool_adapter.rs';s=orig(p)
 for name,ty,slot,size in [('master','PoolV1PairForestMasterV1',48,384),('checkpoint','PoolV1PairForestCheckpointV1',49,192),('lane','PoolV1PairForestLaneStateV1',50,768)]:
  fun='decode_lane_from_pool_release' if name=='lane' else 'decode_'+name+'_box'
  # Native equality contract on an explicitly stated rejection subdomain.
  attrs=f'''#[cfg_attr(kani, kani::requires(NCV_native::domain_{name}(bytes)))]
#[cfg_attr(all(kani, not(ncv_negative)), kani::ensures(|r: &Result<Box<{ty}>,ProgramError>| NCV_native::matches_{name}(r,crate::NCV_reference::decode_{name}_ref(bytes))))]
#[cfg_attr(all(kani, ncv_negative), kani::ensures(|r: &Result<Box<{ty}>,ProgramError>| !NCV_native::matches_{name}(r,crate::NCV_reference::decode_{name}_ref(bytes))))]
'''
  s=s.replace('fn '+fun+'(',attrs+'fn '+fun+'(',1)
 s+='\n#[cfg(kani)] #[path="NCV_native.rs"] mod NCV_native;\n';d[p]=s
 d['programs/r1-cost-probe/src/NCV_native.rs']=(E/'NCV_native.rs').read_text()
 return d
if __name__=='__main__':
 d=files();out=''
 for n,s in d.items():
  try:old=orig(n)
  except subprocess.CalledProcessError:old=''
  out+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 (E/'NCV_harness.patch').write_text(out)
