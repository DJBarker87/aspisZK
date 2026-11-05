"""Explicit-counter reference scopes only; actual-source simulation remains OPEN."""
from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs
rows=json.loads((E/'NIO_FUNCTIONS.json').read_text());index=int(sys.argv[1]);negative=sys.argv[2]=='negative';row=rows[index];name=row['function'].rsplit('::',1)[1]
held2=['process_pair_forest_deposit_with_runtime_v1','process_pair_forest_checkpoint_with_runtime_v1','initialize_pool_accounts_v1']
held3=['process_pair_forest_terminal_with_verifier_v1','process_pair_withdrawal_with_verifier_v1','apply_authorized_append_after_checked_state_v1']
sequential=['process_pair_private_transfer_with_verifier_v1','process_prepare_settlement_with_runtime_v1','process_settle_prepared_with_runtime_v1']
source=r'''
use core::cell::Cell;
use solana_program::program_error::ProgramError;
struct NIO_Cell { counter:Cell<i64>, payload:Cell<u8> }
struct NIO_Guard<'a> { cell:&'a NIO_Cell }
impl Drop for NIO_Guard<'_> {
 fn drop(&mut self) {assert!(self.cell.counter.get()==-1);self.cell.counter.set(0);}
}
fn NIO_acquire(c:&NIO_Cell)->Result<NIO_Guard<'_>,ProgramError>{
 if c.counter.get()==0 {c.counter.set(-1);Ok(NIO_Guard{cell:c})}
 else {Err(ProgramError::AccountBorrowFailed)}
}
struct NIO_Log { next:u8, fail:u8, code:u64 }
fn NIO_payload(g:&NIO_Guard<'_>,l:&mut NIO_Log)->Result<(),ProgramError>{
 assert!(g.cell.counter.get()==-1);g.cell.payload.set(kani::any());
 let tag=l.next;l.next+=1;
 if l.fail==tag {Err(ProgramError::from(l.code))} else {Ok(())}
}
fn NIO_framed_child(c:&NIO_Cell,l:&mut NIO_Log)->Result<(),ProgramError>{
 let n=c.counter.get();assert!(n>=0 && n<i64::MAX);
 c.counter.set(n+1);c.payload.set(kani::any());c.counter.set(c.counter.get()-1);
 let tag=l.next;l.next+=1;
 if l.fail==tag {Err(ProgramError::from(l.code))} else {Ok(())}
}
'''
if name in held2 or name in held3:
 n=2 if name in held2 else 3
 body=''
 for i in range(n):body+=f'let g{i}=NIO_acquire(a[{i}])?;\n'
 if name in ['process_pair_forest_deposit_with_runtime_v1','process_pair_forest_terminal_with_verifier_v1','process_pair_withdrawal_with_verifier_v1','apply_authorized_append_after_checked_state_v1']:body+='NIO_framed_child(a[3],l)?;\n'
 for i in range(n):body+=f'NIO_payload(&g{i},l)?;\n'
 body+='Ok(())'
elif name in sequential:
 body=''
 for i in range(3):body+=f'{{let temporary=NIO_acquire(a[{i}])?;NIO_payload(&temporary,l)?;}}\n'
 body+='Ok(())'
elif name=='close_program_account_v1':
 body='{let temporary=NIO_acquire(a[0])?;NIO_payload(&temporary,l)?;}\nlet n=a[1].counter.get();assert!(n>=0 && n<i64::MAX);a[1].counter.set(n+1);a[1].counter.set(a[1].counter.get()-1);\n{let destination=NIO_acquire(a[2])?;let account=NIO_acquire(a[1])?;NIO_payload(&destination,l)?;NIO_payload(&account,l)?;}\nOk(())'
elif name=='process_withdrawal_with_runtime_v1':
 body='NIO_framed_child(a[3],l)?;{let temporary=NIO_acquire(a[0])?;NIO_payload(&temporary,l)?;}Ok(())'
elif name=='process_pair_forest_initialize_with_runtime_v1':
 body='let master=NIO_acquire(a[0])?;let previous=NIO_acquire(a[1])?;let next=NIO_acquire(a[2])?;NIO_payload(&next,l)?;NIO_payload(&previous,l)?;NIO_payload(&master,l)?;Ok(())'
else:body='let data=NIO_acquire(a[0])?;NIO_payload(&data,l)?;Ok(())'
source+='\nfn NIO_reference(a:[&NIO_Cell;4],l:&mut NIO_Log)->Result<(),ProgramError>{\n'+body+'\n}\n'
setup=''
for i in range(4):
 setup+=f'let n{i}:i64=kani::any();kani::assume(n{i}>=-1);let c{i}=NIO_Cell{{counter:Cell::new(n{i}),payload:Cell::new(kani::any())}};\n'
setup+='kani::assume(n3>=0 && n3<i64::MAX);\n'
if name=='close_program_account_v1':setup+='kani::assume(n0>=0 && n0<i64::MAX && n1>=0 && n1<i64::MAX);\n'
setup+='let cells=[&c0,&c1,&c2];let m0:usize=kani::any();kani::assume(m0<3);let m1:usize=kani::any();kani::assume(m1<3);let m2:usize=kani::any();kani::assume(m2<3);\n'
if name=='close_program_account_v1':setup+='kani::assume(cells[m0].counter.get()>=0 && cells[m0].counter.get()<i64::MAX && cells[m1].counter.get()>=0 && cells[m1].counter.get()<i64::MAX);\n'
setup+='let mut log=NIO_Log{next:0,fail:kani::any(),code:kani::any()};let _result=NIO_reference([cells[m0],cells[m1],cells[m2],&c3],&mut log);\n'
if negative:setup+='if c0.counter.get()==0 {let retained=NIO_acquire(&c0).unwrap();core::mem::forget(retained);}\n'
for i in range(4):setup+=f'assert!(c{i}.counter.get()==n{i});\n'
source+=attrs()+'\n#[kani::proof]\nfn certificate(){'+setup+'}\n'
path=row['path']
stage(path,source,'REFERENCE ONLY: explicit-counter scope candidate',sys.argv[2],'Arbitrary valid i64 counter classes, arbitrary aliases among guard cells; admitted shared room on framed-child/accessor cells. Source function association is not assumed.','Actual frozen-function/source-projection simulation, all reached child footprints and caller entry domains remain OPEN. These reference passes confer NO native source or Pool-consumer credit.',dict(member=row['function'],source_body_sha256=row['body_sha256'],expected_verdict='FAIL' if negative else 'PASS',interpretation='S2TrustedSdkBorrow model candidate only',model_theorems=['NIO_Nested.cleanup_all_counters','NIO_Nested.retained_step','NIE_BorrowRelease.shared_counter_roundtrip'],certificate_status='REFERENCE_ONLY_NOT_ACTUAL_NATIVE'))
print('Explicit-counter reference scope prepared; actual-source association OPEN')
