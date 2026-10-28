from pathlib import Path
import subprocess,os,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def orig(p):return subprocess.check_output(['git','show',REV+':'+p],text=True)
def files():
 p='programs/r1-cost-probe/src/lib.rs';s=orig(p)
 s=s.replace('use aspis_r1_cost_probe::verifier','#![cfg_attr(kani, feature(allocator_api))]\n#[cfg(kani)] extern crate alloc;\nuse aspis_r1_cost_probe::verifier',1)
 s+='\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NDB_KMX;\n#[cfg(kani)] mod NDB_reference;\n'
 d={p:s,'programs/r1-cost-probe/src/NDB_reference.rs':Path('evidence/native-decref-20261028/NCV_reference.rs').read_text()}
 p='programs/r1-cost-probe/src/r1_pool_adapter.rs';d[p]=orig(p)+'\n#[cfg(kani)] #[path="NDB_native.rs"] mod NDB_native;\n'
 d['programs/r1-cost-probe/src/NDB_native.rs']=(E/'NDB_native.rs').read_text().replace('const NDB_INVERSE:bool=false;', 'const NDB_INVERSE:bool='+('true' if os.environ.get('NDB_NEGATIVE') else 'false')+';')
 return d
if __name__=='__main__':
 out=''
 for p,s in files().items():
  try:old=orig(p)
  except subprocess.CalledProcessError:old=''
  out+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p if old else '/dev/null',tofile='b/'+p))
 (E/'NDB_harness.patch').write_text(out)
