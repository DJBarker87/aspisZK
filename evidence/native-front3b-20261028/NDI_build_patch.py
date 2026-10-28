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
   s=s.replace('pub fn state(&self)', '#[cfg_attr(kani,kani::ensures(|r| (*r==NDI_wire::reference::state_ref(self.state)) != cfg!(NDI_invert_state)))]\n    pub fn state(&self)')
   s+='\n#[cfg(kani)] #[path="NDI_wire.rs"] mod NDI_wire;\n'
   s+='\n#[cfg(kani)] pub fn NDI_new_for_backend<H:Digest32>(hash:H,public:&[u8],root:&[u8;32])->Result<([u8;32],u8),Error> {let t=SemanticTranscript::new(hash,public,root)?;Ok((t.state,t.next_row))}\n'
   s+='\n#[cfg(kani)] pub fn NDI_sample_for_backend<H:Digest32>(hash:H,state:[u8;32],next_row:u8,row:u8,framed:&[u8])->Result<([u8;32],[u8;32],u8),Error> {let mut t=SemanticTranscript{hash,state,next_row};let b=t.sample_block_validated(row,framed)?;Ok((b,t.state,t.next_row))}\n'
   s+='\n#[cfg(kani)] pub fn NDI_state_for_backend<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->[u8;32] {SemanticTranscript{hash,state,next_row}.state()}\n'
  if name=='verifier':
   s=s.replace('fn for_query(&self,index:usize)', '#[cfg_attr(kani,kani::requires(self.start<=index && index-self.start<self.inverses.len()))]\n    #[cfg_attr(kani,kani::ensures(|r| (core::ptr::eq(*r,NDI_verifier::reference::geometry_ref(&self.inverses,self.start,index))) != cfg!(NDI_invert_geometry)))]\n    fn for_query(&self,index:usize)')
   s+='\n#[cfg(kani)] #[path="NDI_verifier.rs"] mod NDI_verifier;\n'
  out[p]=s
 for name in ['wire','reference','controls','verifier']:
  out['crates/aspis-r1-cost-probe/src/NDI_'+name+'.rs']=(E/('NDI_'+name+'.rs')).read_text()
 p='programs/r1-cost-probe/src/lib.rs'
 out[p]='#![cfg_attr(kani, feature(allocator_api))]\n'+subprocess.check_output(['git','show',F+':'+p],text=True)+'\n#[cfg(kani)] mod NDI_program;\n#[cfg(kani)] mod NDI_digest;\n'
 out['programs/r1-cost-probe/src/NDI_digest.rs']=(E/'NDI_digest.rs').read_text()
 out['programs/r1-cost-probe/src/NDI_reference.rs']=(E/'NDI_reference.rs').read_text()
 out['programs/r1-cost-probe/src/NDI_program.rs']=(E/'NDI_program.rs').read_text()
 return out
if __name__=='__main__':
 patch=[]
 for p,s in files().items():
  old='' if Path(p).name.startswith('NDI_') else subprocess.check_output(['git','show',F+':'+p],text=True)
  patch+=difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p if old else '/dev/null',tofile='b/'+p)
 (E/'NDI_scratch.patch').write_text(''.join(patch))
