"""Local-record fidelity admission for Result<Box<After/Live>,Error>."""
from NEK_box_context import *

def suite(which,start):
 rp='evidence/slice-s-leaves-20261029/NEC_K032/receipt.json'
 base,_=make(rp);p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';m='crates/aspis-statement/src/pool_v1/NEC_static_decode.rs'
 target='decode_pair_'+('afterstate' if which=='after' else 'live_snapshot')+'_boxed_v1'
 size=688 if which=='after' else 800;kind='After' if which=='after' else 'Live';field='AFTER' if which=='after' else 'LIVE'
 # Retain requires and modifies; replace only this function's ensures by a weak
 # exact-shape postcondition. The real child and Box construction stay intact.
 t=base[p];at=t.index('fn '+target+'(');head=t[:at];a=head.rfind('#[inline(never)]');assert a>=0
 block=head[a:];block=re.sub(r'^#\[cfg_attr\(kani,kani::ensures.*\n','',block,flags=re.M)
 block+='#[cfg_attr(kani,kani::ensures(|r| r.is_ok()))]\n'
 t=head[:a]+block+t[at:];at=t.index('fn '+target+'(');brace=t.index('{',at);end=brace+1;depth=1
 while depth:
  depth+= (t[end]=='{')-(t[end]=='}');end+=1
 bad=t[at:end].replace('fn '+target+'(','fn NEK_bad_modifies(',1).replace('{','{ctx.INPUT=ctx.INPUT.wrapping_add(1);',1)
 # A separate frame field avoids disturbing the child's input pointer assertion.
 bad=bad.replace('ctx.INPUT=ctx.INPUT.wrapping_add(1);','ctx.ROW=ctx.ROW.wrapping_add(1);')
 t+='\n#[cfg(kani)] #[kani::requires(bytes.len()=='+str(size)+')] #[kani::ensures(|r| r.is_ok())] #[kani::modifies()]\n'+bad+'\n';base[p]=t
 init='let mut ctx=NEK_Context::new();let bytes:[u8;'+str(size)+']=kani::any();ctx.'+field+'=kani::any::<'+kind+'>();ctx.INPUT=bytes.as_ptr() as usize;'
 attrs='#[kani::unwind(34)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEK_kmx::KMX_copy_nonoverlapping)]\n'
 for name,stub in [('NEK_shape_contract',False),('NEK_shape_real',False),('NEK_shape_client',True),('NEK_shape_frame',False)]:
  proof='#[kani::proof_for_contract(super::'+target+')]\n' if name=='NEK_shape_contract' else '#[kani::proof_for_contract(super::NEK_bad_modifies)]\n' if name=='NEK_shape_frame' else '#[kani::proof]\n'
  if stub:proof+='#[kani::stub_verified(super::'+target+')]\n'
  call='super::'+('NEK_bad_modifies' if name=='NEK_shape_frame' else target)+'(&mut ctx,&bytes)'
  body='let r='+call+';'
  if name in ['NEK_shape_real','NEK_shape_client']:body+='assert!(matches!(r,Ok(x) if x.next_pair_index==ctx.'+field+'.next_pair_index),"NEK_unimplied_decoder_index");'
  base[m]+='\n'+proof+attrs+'fn '+name+'(){'+init+body+'}\n'
 # Add only valid safe typed nondeterminism for this return shape.
 raw=dict(patched_files((ROOT/'evidence/slice-s-leaves-20261029/NEC_K001/NEC_harness.patch').read_text()))['crates/aspis-statement/src/pool_v1/NEC_arbitrary.rs']
 keep=['PoolV1PairForestTerminalCommonV1','PoolV1PairLatePublicStatementV1','PoolV1PairLiveSnapshotV1','PoolV1PairVerifiedAfterstateV1','PoolV1PairLatePublicStatementErrorV1','PoolV1PairLiveSnapshotErrorV1','PoolV1PairVerifierTransportErrorV1']
 arb='\n'.join(l for l in raw.splitlines() if any('::'+k+' {' in l for k in keep))+'\n'
 base['crates/aspis-statement/src/pool_v1/NEC_arbitrary.rs']=arb
 tests=[('NEK_shape_contract',False),('NEK_shape_contract',True),('NEK_shape_real',False),('NEK_shape_client',True),('NEK_shape_frame',True),('KMX_ptr_positive',False),('KMX_ptr_wrong',True)]
 for i,(name,neg) in enumerate(tests):
  a=f'NEK_K{start+i:03}'
  if (E/a/'receipt.json').exists():continue
  o=dict(base)
  if i==1:o[p]=o[p].replace('kani::ensures(|r| r.is_ok())','kani::ensures(|r| !r.is_ok())')
  harness='NEK_kmx::KMX_checks::'+name if name.startswith('KMX') else 'pool_v1::pair_tree_profile::NEC_static_decode::'+name
  old=os.environ.get('NEK_HARNESS');os.environ['NEK_HARNESS']=harness
  try:v=publish(a,rp,o,neg,which+' decoder exact Result<Box<Record>,Error> shape admission: '+name)
  finally:
   if old is None:os.environ.pop('NEK_HARNESS',None)
   else:os.environ['NEK_HARNESS']=old
  if v=='OPEN':break
if __name__=='__main__':suite(sys.argv[1],int(sys.argv[2]))
