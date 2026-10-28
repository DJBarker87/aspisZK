from pathlib import Path
import difflib,sys
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E))
from NCN_expected import expected
import tempfile,subprocess

def current():
 manifest=expected(E/'NCN_raw.patch')
 with tempfile.TemporaryDirectory() as d:
  for name in manifest['after']:
   p=Path(d)/name;p.parent.mkdir(parents=True,exist_ok=True)
   r=subprocess.run(['git','show','4bb3b3f5:'+name],capture_output=True)
   if r.returncode==0:p.write_bytes(r.stdout)
  for x in manifest['patch_chain']:
   r=subprocess.run(['git','apply','-'],input=Path(x['path']).read_bytes(),cwd=d,capture_output=True);assert r.returncode==0,r.stderr
  return (Path(d)/'crates/aspis-r1-cost-probe/src/verifier.rs').read_text()
def extend(name,h):
 s=current()
 (E/name).write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+h).splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier.rs')))
attrs='''#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,NCI_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,NCI_kmx::KMX_copy_from_slice)]
'''
