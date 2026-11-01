from NEK_priority import *
from NEK_recover import recover

def nbc(start=5):
 rp='evidence/native-tx2a-20261027/NBC_K003/receipt.json';sources,missing=recover(rp);assert not missing,missing
 mod='crates/aspis-r1-cost-probe/src/verifier/NBC_runtime.rs'
 body=next(v for n,v in sources.items() if n.endswith('/verifier/NBC_runtime.rs'))
 # Unselected observer None check is not compiled, and remains K-2 quarantined.
 body=body[body.index('#[kani::proof]\nfn NBC_trace_value'):]
 body=body.replace('crate::trace::value(tag,index,x);','crate::trace::value(tag,index,x);\n assert!(true);')
 o=kmx('crates/aspis-r1-cost-probe');p='crates/aspis-r1-cost-probe/src/verifier.rs';o[p]=frozen(p).decode()+'\n#[cfg(kani)] mod NBC_runtime;\n';o[mod]=body
 w='crates/aspis-core/src/field/wide_exact.rs';o[w]=frozen(w).decode()+'\n#[cfg(kani)] mod NBC_runtime;\n';o['crates/aspis-core/src/field/wide_exact/NBC_runtime.rs']=next(v for n,v in sources.items() if n.endswith('/wide_exact/NBC_runtime.rs'))
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo[mod]=body.replace('assert!(true);','assert!(false);')
  publish(a,rp,oo,neg,'exact recovered original no-panic trace-value call; original name, negative control after real call; no writable static')

def nde_binary(start=7):
 rp='evidence/native-front2-20261028/NDE_K071/receipt.json';s=ROOT/Path(rp).parent/'sources/NDE_src';p='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';m='crates/aspis-statement/src/pool_v1/NDE_copy.rs'
 old=(s/p).read_text();h=(s/m).read_text();head=h[:h.index('#[kani::stub')];one=h[h.index('#[kani::stub',h.index('fn NDE_stub_log')):h.index('#[kani::stub',h.index('fn NDE_binary'))]
 # Keep only selected_binary contract; unrelated contracts are removed, bodies unchanged.
 import re
 old='\n'.join(l for l in old.splitlines() if not('cfg_attr(kani' in l and 'NDE_simple_invert' not in l))+'\n'
 o=kmx('crates/aspis-statement');o[p]=old;o[m]=(head+one).replace('crate::NDE_kmx','crate::NEK_kmx');o['crates/aspis-statement/src/pool_v1/NDE_reference.rs']=(s/'crates/aspis-statement/src/pool_v1/NDE_reference.rs').read_text()
 c='crates/aspis-core/src/lib.rs';o[c]=frozen(c).decode()+'\n#[cfg(kani)] mod NEK_arbitrary;\n';o['crates/aspis-core/src/NEK_arbitrary.rs']=(s/'crates/aspis-core/src/NDE_arbitrary.rs').read_text()
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo[p]=old.replace('!= cfg!(NDE_simple_invert)','== cfg!(NDE_simple_invert)')
  publish(a,rp,oo,neg,'original proof_for_contract; unselected static modules omitted; native selected body unchanged')



def nbg_square(start=9):
 rp='evidence/native-tx2c-20261027/NBG_K028/receipt.json';p='crates/aspis-core/src/field.rs';m='crates/aspis-core/src/field/NBG_runtime.rs'
 h=(ROOT/'evidence/native-tx2c-20261027/NBG_lastfield.rs').read_text()
 h=h.replace('static mut NBG_PRODUCT:u32=0;\nstatic mut NBG_MUL_CALLS:usize=0;','struct NEK_Context{NBG_PRODUCT:u32,NBG_MUL_CALLS:usize}\nimpl NEK_Context{')
 h=h.replace('fn NBG_product(x:','fn NBG_product(&mut self,x:').replace('unsafe{NBG_PRODUCT=r;NBG_MUL_CALLS+=1;}','self.NBG_PRODUCT=r;self.NBG_MUL_CALLS+=1;')
 h=h.replace('#[kani::proof]','}\n#[kani::proof]',1).replace('#[kani::stub(super::M31::mul,NBG_product)]\n','')
 h=h.replace('fn NBG_square_iteration(){','fn NBG_square_iteration(){\n let mut ctx=NEK_Context{NBG_PRODUCT:0,NBG_MUL_CALLS:0};')
 h=h.replace('unsafe{NBG_MUL_CALLS=0;}','ctx.NBG_MUL_CALLS=0;').replace('value=value.mul(value);','value=ctx.NBG_product(value,value);')
 h=h.replace('unsafe{assert!(value.0==NBG_PRODUCT);assert!(NBG_MUL_CALLS==1);}','assert!(value.0==ctx.NBG_PRODUCT);assert!(ctx.NBG_MUL_CALLS==1);').replace('unsafe{assert!(NBG_MUL_CALLS==0);}','assert!(ctx.NBG_MUL_CALLS==0);')
 assert 'static' not in h
 o=kmx('crates/aspis-core');o[p]=frozen(p).decode()+'\n#[cfg(kani)] mod NBG_runtime;\n';o[m]=h
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo[m]=h.replace('assert!(ctx.NBG_MUL_CALLS==1);','assert!(ctx.NBG_MUL_CALLS!=1);')
  publish(a,rp,oo,neg,'same one-iteration property, all raw u32 domain; local multiplication log; LPf_BaseMultiply.source retained, no native multiplication')



def nbq_error(start=11):
 rp='evidence/native-tx2h-20261028/NBQ_K016/receipt.json';p='programs/r1-cost-probe/src/lib.rs'
 original=frozen(p).decode()
 h=dict(patched_files((ROOT/'evidence/native-tx2h-20261028/NBQ_K016-harness.patch').read_text()))[p]
 h=h[h.index('#[cfg(kani)]\nmod NBQ_error_control'):]
 h=h.replace('static mut CALLS:usize=0;','pub(super) struct NEK_Context{pub(super) CALLS:usize}\nimpl NEK_Context{pub(super) fn private_log(&mut self,_s:&str){self.CALLS+=1;}}')
 h=h.replace('fn private_log(_s:&str){unsafe{CALLS+=1;}}','')
 h=h.replace('#[kani::stub(solana_program::log::sol_log,private_log)]','')
 h=h.replace('fn rejects(){','fn rejects(){\n let mut ctx=NEK_Context{CALLS:0};')
 h=h.replace('unsafe{CALLS=0;}','ctx.CALLS=0;').replace('super::error(error)','super::error(error,&mut ctx)').replace('unsafe{assert!(CALLS==1);}','assert!(ctx.CALLS==1);')
 old='fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}'
 new='fn error(e:verifier::Error,ctx:&mut NBQ_error_control::NEK_Context)->ProgramError{ctx.private_log(&std::fmt::format(format_args!("r1:error:{:?}",e)));ProgramError::InvalidInstructionData}'
 assert old in original
 native=original.replace(old,new).replace('.map_err(error)','.map_err(|e|error(e,&mut NBQ_error_control::NEK_Context{CALLS:0}))')
 o=kmx('programs/r1-cost-probe');o[p]+='\n'+h # replace native only, preserving own KMX module
 o[p]=o[p].replace(original,native,1)
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo[p]=o[p].replace('assert!(ctx.CALLS==1);','assert!(ctx.CALLS!=1);')
  publish(a,rp,oo,neg,'error native-step explicit local log receiver; same formatting abstraction, invalid-data result and one-call assertion; msg expansion association retained')



def nbp_debug(start=13):
 rp='evidence/native-tx2g-20261028/NBP_K002/receipt.json';d=read_json(E/'NEK_NBP_K002_recovered.json.xz');h=next(iter(d.values()));h=h[h.index('use core::fmt::Write;'):]
 assert 'static mut' not in h
 o=kmx('programs/r1-cost-probe');o['programs/r1-cost-probe/src/lib.rs']+='\n#[cfg(kani)] mod NBP_error;\n';o['programs/r1-cost-probe/src/NBP_error.rs']=h
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo['programs/r1-cost-probe/src/NBP_error.rs']=h.replace('assert!(w.seen==5);','assert!(w.seen!=5);')
  publish(a,rp,oo,neg,'exact recovered local Writer byte/length check; unselected static log module omitted')

if __name__=='__main__':globals()[sys.argv[1]](int(sys.argv[2]))
