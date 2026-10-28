from pathlib import Path
import subprocess,difflib,os
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 out={};patch=[]
 def put(n,s,base=''):
  out[n]=s
  patch.append(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='a/'+n if base else '/dev/null',tofile='b/'+n)))
 def base(n):return subprocess.check_output(['git','show',REV+':'+n],text=True)
 n='programs/r1-cost-probe/src/lib.rs';b=base(n)
 s='#![cfg_attr(kani, feature(allocator_api))]\n'+b+'\n#[cfg(kani)]\nmod NDG_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n'
 put(n,s,b)
 n='programs/r1-cost-probe/src/r1_pool_adapter.rs';b=base(n);s=b
 for name,ens in [('pool_program_id','*r == NDG_native::reference::pool_id_ref()'),('registry_program_id','*r == NDG_native::reference::registry_id_ref()'),('readonly_buffer_meta_ok','match r {Ok(())=>NDG_native::reference::readonly_buffer_ref(is_signer,is_writable,executable),Err(ProgramError::InvalidAccountData)=>!NDG_native::reference::readonly_buffer_ref(is_signer,is_writable,executable),_=>false}'),('readonly_meta_ok','match r {Ok(())=>NDG_native::reference::readonly_ref(owner!=expected,is_signer,is_writable,executable),Err(ProgramError::InvalidAccountData)=>!NDG_native::reference::readonly_ref(owner!=expected,is_signer,is_writable,executable),_=>false}')]:
  s=s.replace('fn '+name+'(',f'#[cfg_attr(kani, kani::ensures(|r| ({ens}) != cfg!(NDG_invert_{name}))) ]\nfn '+name+'(',1)
 s+='\n#[cfg(kani)]\n#[path="NDG_native.rs"]\nmod NDG_native;\n';put(n,s,b)
 n='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';b=base(n);s=b
 for name in ['key','owner']:
  s=s.replace('    fn '+name+'(',f'    #[cfg_attr(kani, kani::ensures(|r| (*r == &self.{name}) && core::ptr::eq(*r,&self.{name}) != cfg!(NDG_invert_{name}))) ]\n    fn '+name+'(',1)
 s=s.replace('    fn data_len(', '#[cfg_attr(kani, kani::ensures(|r| (*r == self.length) != cfg!(NDG_invert_data_len)))]\n    fn data_len(',1)
 s=s.replace('    fn data(', '#[cfg_attr(kani, kani::ensures(|r| (match (&self.bytes,r) { (Ok(b),Ok(v)) => b.as_slice()==*v, (Err(e),Err(f))=>e==f, _=>false }) != cfg!(NDG_invert_data)))]\n    fn data(',1)
 s+='\n#[cfg(kani)]\n#[path="NDG_owned.rs"]\nmod NDG_owned;\n';put(n,s,b)
 for n in ['NDG_reference','NDG_native','NDG_owned']:
  put('programs/r1-cost-probe/src/'+n+'.rs',(E/(n+'.rs.txt')).read_text())
 inverted=os.environ.get('NDG_INVERT')
 if inverted:
  for n in list(out):out[n]=out[n].replace('cfg!(NDG_invert_'+inverted+')','true')
  patch=[]
  for n,s in out.items():
   p=subprocess.run(['git','show',REV+':'+n],capture_output=True,text=True);b=p.stdout if p.returncode==0 else ''
   patch.append(''.join(difflib.unified_diff(b.splitlines(True),s.splitlines(True),fromfile='a/'+n if b else '/dev/null',tofile='b/'+n)))
 (E/'NDG_native.patch').write_text(''.join(patch));return out
if __name__=='__main__':files()
