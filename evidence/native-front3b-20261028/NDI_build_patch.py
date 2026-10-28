from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 out={}
 for name in ['lib','r1_wire','candidate','verifier','compact']:
  p='crates/aspis-r1-cost-probe/src/'+name+'.rs';s=subprocess.check_output(['git','show',F+':'+p],text=True)
  if name=='lib':s='#![cfg_attr(kani, feature(allocator_api))]\n'+s+'\n#[cfg(kani)] mod NDI_controls;\n'
  if name=='r1_wire':
   s=s.replace('pub(crate) fn row(&self)', '#[cfg_attr(kani,kani::ensures(|r| (*r==NDI_wire::reference::validated_row_ref(self.row)) != cfg!(NDI_invert_row)))]\n    pub(crate) fn row(&self)')
   s+='\n#[cfg(kani)] #[path="NDI_wire.rs"] mod NDI_wire;\n'
  out[p]=s
 for name in ['wire','reference','controls']:
  out['crates/aspis-r1-cost-probe/src/NDI_'+name+'.rs']=(E/('NDI_'+name+'.rs')).read_text()
 return out
if __name__=='__main__':
 patch=[]
 for p,s in files().items():
  old='' if Path(p).name.startswith('NDI_') else subprocess.check_output(['git','show',F+':'+p],text=True)
  patch+=difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p if old else '/dev/null',tofile='b/'+p)
 (E/'NDI_scratch.patch').write_text(''.join(patch))
