"""Full mutable child oracle, exact Result/order, ONE subsequent KMX copy step."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','wrong_after','wrong_byte']
subprocess.run([sys.executable,str(E/'NEM_prepare_array_contract.py'),'oracle_support'],check=True)
patch=(E/'NEM_native_contracts.patch').read_text();head,rest=patch.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_slice_contract.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'))
old=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();error=next(l[1:] for l in old.splitlines() if l.startswith('+fn NEE_any_PoolV1PairVerifierTransportErrorV1')).replace('NEE_any_PoolV1PairVerifierTransportErrorV1','any_after_error')
body+=error+'\n'+'''
fn afterstate()->PoolV1PairVerifiedAfterstateV1{PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:[NODES]}}
struct TailFrame<'a>{expected:&'a PoolV1PairLatePublicStatementV1,other:&'a PoolV1PairVerifiedAfterstateV1,after_reply:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>,live:Result<(),PoolV1PairLiveSnapshotErrorV1>,calls:u8,j:usize,post:u8,offset:usize}
fn child_after(s:&PoolV1PairVerifiedAfterstateV1,f:&mut TailFrame)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{assert!(f.calls==1 && core::ptr::eq(s,&f.expected.candidate_afterstate),"actual candidate child after snapshot success");f.calls=2;f.after_reply}
fn tail(s:&PoolV1PairLatePublicStatementV1,out:&mut[u8;1520],f:&mut TailFrame)->Result<(),PoolV1PairLatePublicStatementErrorV1>{
 assert!(core::ptr::eq(&s.live_snapshot,&f.expected.live_snapshot));let base=out.as_mut_ptr();let window=&mut out[32..832];assert!(window.len()==800&&window.as_mut_ptr()==base.wrapping_add(32));
 let array:&mut[u8;800]=window.try_into().unwrap();assert!(array.as_mut_ptr()==base.wrapping_add(32));let reply=weak(&s.live_snapshot,array,kani::any());f.live=reply;f.calls=1;f.post=out[f.j];
 reply.map_err(|error| PoolV1PairLatePublicStatementErrorV1::Snapshot(error))?;
 let bytes=child_after(AFTER,f).map_err(|error| PoolV1PairLatePublicStatementErrorV1::Afterstate(error))?;
 let dst=&mut out[832..];let src=&bytes;let mut i=f.offset;dst[i]=src[i]CORRUPT;i+=1;assert!(i==f.offset+1);
 Ok(())
}
#[kani::proof]
#[kani::stub_verified(weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn tail_control(){let s=PoolV1PairLatePublicStatementV1{live_snapshot:snapshot(),candidate_afterstate:afterstate()};let other=afterstate();let mut output:[u8;1520]=kani::any();let j:usize=kani::any();kani::assume(j<1520);let offset:usize=kani::any();kani::assume(offset<688);let mut f=TailFrame{expected:&s,other:&other,after_reply:if kani::any(){Ok(kani::any())}else{Err(any_after_error())},live:Ok(()),calls:0,j,post:0,offset};
 let actual=tail(&s,&mut output,&mut f);let expected=match f.live{Err(e)=>Err(PoolV1PairLatePublicStatementErrorV1::Snapshot(e)),Ok(())=>match f.after_reply{Err(e)=>Err(PoolV1PairLatePublicStatementErrorV1::Afterstate(e)),Ok(_)=>Ok(())}};
 assert!(actual==expected && f.calls==if f.live.is_err(){1}else{2},"full native Result and child order");
 let expected_byte=if f.live.is_ok()&&f.after_reply.is_ok()&&j==832+offset{match f.after_reply{Ok(bytes)=>bytes[offset],_=>0}}else{f.post};
 assert!(output[j]==expected_byte,"same whole child poststate, exact suffix reply and complete prestate frame");
}
'''.replace('NODES',','.join(['digest()']*20)).replace('AFTER','f.other' if mode=='wrong_after' else '&s.candidate_afterstate').replace('CORRUPT','^1' if mode=='wrong_byte' else '')
patch=head+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_slice_contract.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines());(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_LATE_TAIL_CURRENT.json').write_text(json.dumps(dict(mode=mode,full_arbitrary_live_Result=True,full_arbitrary_snapshot_mutation=True,full_arbitrary_after_Result=True,one_KMX_copy_iteration=True,exact_same_actual_child_places=True,arbitrary_full_prestate=True,observed_cell='arbitrary cell after actual full child mutation; retained through rejection or updated only at selected suffix copy cell',method='ruling y with per-shape ruling t full-slice contract controls; rule B on suffix copy',no_writable_static=True,trust_classification='P6/D188 option A reclassification'),indent=1)+'\n')
