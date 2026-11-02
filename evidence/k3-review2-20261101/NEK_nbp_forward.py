"""Preserve NBP formatting/log byte and pointer observations in an explicit context."""
from NEK_more import *
def run(start=301):
 rp='evidence/native-tx2g-20261028/NBP_K040/receipt.json';sources,missing=recover(rp);assert not missing
 h=next(iter(sources.values()));h=h[h.index('fn NBP_format_reply'):]
 h=h.replace('fn NBP_format_reply(_args:', 'fn NBP_format_reply(&mut self,_args:').replace('NBP_FORMAT_PTR=s.as_ptr()','self.NBP_FORMAT_PTR=s.as_ptr()')
 h=h.replace('fn NBP_log_reply(s:', 'fn NBP_log_reply(&mut self,s:').replace('==NBP_FORMAT_PTR','==self.NBP_FORMAT_PTR').replace('NBP_CALLS+=1','self.NBP_CALLS+=1')
 split=h.index('#[kani::proof]');methods=h[:split];harness=h[split:]
 harness=re.sub(r'^#\[kani::stub.*\n','',harness,flags=re.M).replace('fn NBP_error_forward() {','fn NBP_error_forward() {let mut ctx=NEK_Context{NBP_FORMAT_PTR:core::ptr::null(),NBP_CALLS:0};')
 harness=harness.replace('NBP_CALLS=0','ctx.NBP_CALLS=0').replace('NBP_CALLS==1','ctx.NBP_CALLS==1').replace('super::error(e)','super::error(e,&mut ctx)')
 harness=harness.replace('#[kani::proof]','#[kani::proof]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEK_kmx::KMX_copy_nonoverlapping)]',1)
 h='pub(super) struct NEK_Context{NBP_FORMAT_PTR:*const u8,NBP_CALLS:usize}\nimpl NEK_Context{pub(super) fn new()->Self{Self{NBP_FORMAT_PTR:core::ptr::null(),NBP_CALLS:0}}\n'+methods.replace('fn NBP_', 'pub(super) fn NBP_')+'}\n'+harness
 p='programs/r1-cost-probe/src/lib.rs';old=frozen(p).decode();signature='fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}'
 new='fn error(e:verifier::Error,ctx:&mut NBP_error::NEK_Context)->ProgramError{let s=ctx.NBP_format_reply(format_args!("r1:error:{:?}",e));ctx.NBP_log_reply(&s);ProgramError::InvalidInstructionData}'
 assert signature in old
 native=old.replace(signature,new).replace('.map_err(error)','.map_err(|e|error(e,&mut NBP_error::NEK_Context::new()))')
 o=kmx('programs/r1-cost-probe');o[p]=o[p].replace(old,native,1)+'\n#[cfg(kani)] mod NBP_error;\n';o['programs/r1-cost-probe/src/NBP_error.rs']=h
 own='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';o[own]=frozen(own).decode().replace('.map_err(super::super::error)','.map_err(|e|super::super::error(e,&mut super::super::NBP_error::NEK_Context::new()))')
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo['programs/r1-cost-probe/src/NBP_error.rs']=h.replace('assert!(ctx.NBP_CALLS==1)','assert!(ctx.NBP_CALLS!=1)')
  v=publish(a,rp,oo,neg,'same format-reply abstraction and native msg expansion; local pointer/byte/call log; exact original error result and name')
  if v=='OPEN':break
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 301)
