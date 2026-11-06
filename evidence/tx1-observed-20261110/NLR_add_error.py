from pathlib import Path
P=Path(__file__).resolve().parent
s=(P/'NLR_native.rs.txt').read_text()
old=Path('evidence/tx1-prepare-20261110/NLJ_native.rs.txt').read_text()
start=old.index('fn error()');end=old.index('\nstruct Log',start)
s+='\n'+old[start:end]+'\n'
s+='''fn parse_error(bad:bool){let e=error();let r=parse_window(Err::<'static_prefix,Error>(e));let good=matches!(r,Err(actual)if actual==e);if bad{assert!(!good)}else{assert!(good)}}
'''.replace("Err::<'static_prefix,Error>(e)","Err::<Prefix<'static>,Error>(e)")
s+='''#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse_error_cut(){parse_error(false)}
#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn parse_error_control(){parse_error(true)}
#[kani::proof] #[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn independent_error_control(){let expected=error();let input:u8=kani::any();let coupled=if input%2==0{Error::Terminal}else{Error::Public};assert_eq!(coupled,expected)}
'''
(P/'NLR_native.rs.txt').write_text(s)
