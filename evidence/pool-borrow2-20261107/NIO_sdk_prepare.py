"""Typed SDK carrier fidelity; no fabricated guards and no production caller credit."""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs,account_setup
kind=int(sys.argv[1]);carrier=int(sys.argv[2]);negative=sys.argv[3]=='negative'
mut=kind in [1,3];data=kind<2;field='data' if data else 'lamports';op='try_borrow_'+('mut_' if mut else '')+field;life="i" if mut else "b";typ="&'"+life+(" mut [u8]" if data else " mut u64");guard='RefMut' if mut else 'Ref'
head=f"fn NIO_get<'b,'i>(a:&'b solana_program::account_info::AccountInfo<'i>,b:&'b solana_program::account_info::AccountInfo<'i>,c:&'b solana_program::account_info::AccountInfo<'i>)->Result<core::cell::{guard}<'b,{typ}>,solana_program::program_error::ProgramError>{{\n"
head+=('let result=b.' if negative else 'let result=a.')+op+'();\n'
if carrier==0:head+='result\n'
elif carrier==1:head+='match result {Ok(g)=>{let moved=Some(g);Ok(moved.unwrap())},Err(e)=>Err(e)}\n'
else:head+='match result {Ok(g)=>{let mut moved=alloc::vec::Vec::with_capacity(1);moved.push(g);moved.push(c.'+op+'()?);drop(moved.pop());Ok(moved.pop().unwrap())},Err(e)=>Err(e)}\n'
head+='}\n'
s=account_setup(3)
read=(lambda a: a+'.try_borrow_data().unwrap()[0]') if data else (lambda a:a+'.lamports()')
s+='let before='+read('a0')+';let before_b='+read('a1')+';let before_c='+read('a2')+';let written:'+('u8' if data else 'u64')+'=kani::any();let n:u8=kani::any();kani::assume(n<4);\n'
s+=f'let h0=if n==1 || n==2 {{Some(a0.try_borrow_{field}().unwrap())}}else{{None}};let h1=if n==2 {{Some(a0.try_borrow_{field}().unwrap())}}else{{None}};let x=if n==3 {{Some(a0.try_borrow_mut_{field}().unwrap())}}else{{None}};\n'
s+='let initial=if n==3 {-1i64}else{n as i64};let mut model_counter=initial;let result=NIO_get(&a0,&a1,&a2);let expected_ok='+('n==0' if mut else 'n!=3')+';\n'
s+='match result {Ok(mut g)=>{assert!(expected_ok);model_counter='+('-1' if mut else 'initial+1')+';'
s+=f'assert!(a0.try_borrow_mut_{field}().is_err());assert!(a1.try_borrow_mut_{field}().is_ok());assert!(a2.try_borrow_mut_{field}().is_ok());'
if mut:s+=('g[0]=written;' if data else '**g=written;')
else:s+=('assert!(g[0]==before);' if data else 'assert!(**g==before);')
s+='drop(g);model_counter='+('0' if mut else 'model_counter-1')+';},Err(e)=>{assert!(!expected_ok);assert!(e==ProgramError::AccountBorrowFailed);}}\n'
s+='assert!(model_counter==initial);'
s+=f'assert!(a0.try_borrow_mut_{field}().is_ok()==(n==0));assert!(a1.try_borrow_mut_{field}().is_ok());assert!(a2.try_borrow_mut_{field}().is_ok());drop(h1);drop(h0);drop(x);assert!(a0.try_borrow_mut_{field}().is_ok());\n'
s+='assert!('+read('a0')+'=='+('if expected_ok {written}else{before}' if mut else 'before')+');assert!('+read('a1')+'==before_b);assert!('+read('a2')+'==before_c);\n'
source=head+attrs()+'\n#[kani::proof]\nfn certificate(){'+s+'}\n'
stage('programs/aspis-pool/src/processor.rs',source,'typed actual SDK guard-carrier fidelity',sys.argv[3],'Actual SDK data/lamport guard, shared/exclusive; valid locally owned shared counts 0..2 or one exclusive token; direct/Option/Vec move carriers.','Finite carrier calibration only: actual Pool caller/source association and arbitrary numeric ambient counter remains OPEN. Lamport-wrapper implementation is not added to the data-only SDK trust item.',dict(kind_index=kind,carrier_index=carrier,expected_verdict='FAIL' if negative else 'PASS',native_credit='LOCAL_SDK_FIDELITY_ONLY',model_theorems=['NIE_BorrowRelease.shared_counter_roundtrip','NIO_Nested.cleanup_all_counters'],control='Safe constructor returns a guard on the wrong live account; no integer-word fabrication.'))
print('Typed SDK guard carrier prepared')
