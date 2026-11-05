"""Minimal typed-guard counter-context calibration across carrier representations."""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs,account_setup
container=sys.argv[1];mut=sys.argv[2]=='mut';carrier=int(sys.argv[3]);negative=sys.argv[4]=='negative';op='try_borrow_mut' if mut else 'try_borrow'
body='use core::cell::RefCell;\n'
if container=='stack_scalar':
 body+='let c0=RefCell::new(kani::any::<u64>());let c1=RefCell::new(kani::any::<u64>());\n';get0='c0.'+op+'()';get1='c1.'+op+'()';probe0='c0.try_borrow_mut()';probe1='c1.try_borrow_mut()'
elif container in ['stack_slice','rc_slice']:
 body+='let mut d0=[kani::any::<u8>()];let mut d1=[kani::any::<u8>()];\n'
 wrap='alloc::rc::Rc::new(' if container=='rc_slice' else '';end=')' if wrap else ''
 body+='let c0='+wrap+'RefCell::new(d0.as_mut_slice())'+end+';let c1='+wrap+'RefCell::new(d1.as_mut_slice())'+end+';\n';get0='c0.'+op+'()';get1='c1.'+op+'()';probe0='c0.try_borrow_mut()';probe1='c1.try_borrow_mut()'
else:
 body+=account_setup(2);field='data' if container=='sdk_data' else 'lamports';get0='a0.'+op+'_'+field+'()';get1='a1.'+op+'_'+field+'()';probe0='a0.try_borrow_mut_'+field+'()';probe1='a1.try_borrow_mut_'+field+'()'
body+='let result='+ (get1 if negative else get0)+';\n'
body+='let guard=match result {Ok(g)=>g,Err(_)=>{assert!(false);return}};\n'
if carrier==1:body+='let moved=Some(guard);let guard=match moved {Some(g)=>g,None=>{assert!(false);return}};\n'
if carrier==2:body+='let mut moved=alloc::vec::Vec::with_capacity(1);moved.push(guard);let guard=match moved.pop() {Some(g)=>g,None=>{assert!(false);return}};\n'
body+='assert!('+probe0+'.is_err());assert!('+probe1+'.is_ok());drop(guard);assert!('+probe0+'.is_ok());assert!('+probe1+'.is_ok());\n'
source=attrs()+'\n#[kani::proof]\nfn certificate(){'+body+'}\n'
stage('programs/aspis-pool/src/processor.rs',source,'minimal typed guard counter-context fidelity',sys.argv[4],'Locally owned initially free cells; safe native constructors; typed direct/Option/Vec guard moves; no payload dereference, byte-formatting, fabricated guard or writable static.','Representation calibration only. Actual Pool caller/source association and arbitrary incoming counter relation remain OPEN.',dict(container=container,exclusive=mut,carrier=carrier,expected_verdict='FAIL' if negative else 'PASS',control='Native constructor obtains guard from the other live cell; counter-context assertion must fail.',native_credit='LOCAL_FIDELITY_ONLY'))
print('Minimal typed counter-context calibration prepared')
