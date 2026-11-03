"""Actual encoder tail: arbitrary full late mutation, Result/order and one suffix step."""
from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','wrong_late','wrong_payment','wrong_byte']
subprocess.run([sys.executable,str(E/'NEQ_prepare_late_contract.py'),'oracle_support'],check=True)
p=E/'NEQ_native_contracts.patch';patch=p.read_text();head,rest=patch.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_slice_contract.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'))
old=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text();a=old.index('+fn NEE_digest()');z=old.index('+#[derive',a);construct='\n'.join(l[1:] for l in old[a:z].splitlines() if l.startswith('+')).replace('super::super::PoolV1PairLiveSnapshotV1','PoolV1PairLiveSnapshotV1')
body+=construct+'\n'+'''
struct TailFrame<'a>{expected:&'a PoolV1PairForestTerminalStatementV1,other:&'a PoolV1PairForestTerminalStatementV1,pay:Result<[u8;216],PoolV1PaymentStatementFormatError>,late:Result<(),PoolV1PairLatePublicStatementErrorV1>,calls:u8,j:usize,post:u8,offset:usize}
fn pay(s:&PoolV1PairForestTerminalStatementV1,f:&mut TailFrame)->Result<[u8;216],PoolV1PaymentStatementFormatError>{
 assert!(f.calls==1,"payment follows successful late call");
 match(s,f.expected){(PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:p,..},PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:q,..})=>assert!(core::ptr::eq(p,q)),(PoolV1PairForestTerminalStatementV1::Withdrawal{public:p,..},PoolV1PairForestTerminalStatementV1::Withdrawal{public:q,..})=>assert!(core::ptr::eq(p,q)),_=>assert!(false)}
 f.calls=2;f.pay
}
fn tail(s:&PoolV1PairForestTerminalStatementV1,out:&mut[u8;1880],f:&mut TailFrame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{
 let common=s.common();let late=LATE;
 assert!(core::ptr::eq(late,&f.expected.common().lane_transition));
 let base=out.as_mut_ptr();let window=&mut out[144..1664];assert!(window.len()==1520&&window.as_mut_ptr()==base.wrapping_add(144));
 let array:&mut[u8;1520]=window.try_into().unwrap();assert!(array.as_mut_ptr()==base.wrapping_add(144));let reply=weak(late,array,kani::any());f.late=reply;f.calls=1;f.post=out[f.j];
 reply.map_err(|error|PoolV1PairForestTerminalFormatErrorV1::LaneTransition(error))?;
 let payment=pay(PAYMENT,f).map_err(|error|PoolV1PairForestTerminalFormatErrorV1::Payment(error))?;
 let dst=&mut out[1664..];let src=&payment;let mut i=f.offset;dst[i]=src[i]CORRUPT;i+=1;assert!(i==f.offset+1);Ok(())
}
#[kani::proof]
#[kani::stub_verified(weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn encoder_tail(){let s=NEE_statement();let other=NEE_statement();let mut output:[u8;1880]=kani::any();let j:usize=kani::any();kani::assume(j<1880);let offset:usize=kani::any();kani::assume(offset<216);let mut f=TailFrame{expected:&s,other:&other,pay:if kani::any(){Ok(kani::any())}else{Err(NEE_any_PoolV1PaymentStatementFormatError())},late:Ok(()),calls:0,j,post:0,offset};
 let actual=tail(&s,&mut output,&mut f);let expected=match f.late{Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition(e)),Ok(())=>match f.pay{Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e)),Ok(_)=>Ok(())}};
 assert!(actual==expected&&f.calls==if f.late.is_err(){1}else{2},"complete native Result and child order");
 let expected_byte=if f.late.is_ok()&&f.pay.is_ok()&&j==1664+offset{match f.pay{Ok(bytes)=>bytes[offset],_=>0}}else{f.post};assert!(output[j]==expected_byte,"same child poststate and complete suffix-step frame");
}
'''.replace('LATE','&f.other.common().lane_transition' if mode=='wrong_late' else '&common.lane_transition').replace('PAYMENT','f.other' if mode=='wrong_payment' else 's').replace('CORRUPT','^1' if mode=='wrong_byte' else '')
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_slice_contract.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines()))
(E/'NEQ_ENCODER_TAIL_CURRENT.json').write_text(json.dumps(dict(mode=mode,late_modifies=[144,1664],payment_write=[1664,1880],all_Result_variants=True,arbitrary_prestate=True,one_KMX_step=True,exact_child_places=True,classification='ruling y oracle with full fixed1520 mutation; rule B suffix step; t shape controls K002-010',trust='P6/D188 option A reclassification'),indent=1)+'\n')
