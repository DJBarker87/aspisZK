use super::*;
static mut NBR_BASE:*const u8=core::ptr::null();
static mut NBR_CHECKED:bool=false;
static mut NBR_ACCEPT:bool=false;
static mut NBR_ENTERED:bool=false;
fn NBR_check_values(bytes:&[u8])->Result<(),CodecError>{unsafe{
 assert!(!NBR_ENTERED);NBR_ENTERED=true;
 assert_eq!(bytes.as_ptr(),NBR_BASE.add(7031));assert_eq!(bytes.len(),464);
 NBR_CHECKED=NBR_ACCEPT;
 if NBR_ACCEPT{Ok(())}else{Err(CodecError::NonCanonical)}
}}
fn NBR_first_echeck(bytes:&[u8],k:bool)->Result<(),Error>{unsafe{
 assert!(NBR_ENTERED&&NBR_CHECKED);assert_eq!(bytes.as_ptr(),NBR_BASE.add(7495));assert_eq!(bytes.len(),32);assert!(!k);
 kani::cover!(true,"first echeck is reached only after SAME compact check succeeds");
 kani::assume(false);Ok(())
}}
#[kani::proof] #[kani::unwind(2)]
#[kani::stub(crate::compact::check_values,NBR_check_values)]
#[kani::stub(crate::verifier::echeck,NBR_first_echeck)]
fn NBR_scan_check_cut(){
 let proof:[u8;57607]=kani::any();unsafe{NBR_BASE=proof.as_ptr();NBR_CHECKED=false;NBR_ACCEPT=kani::any();NBR_ENTERED=false;}
 let r=canonical_scan(&proof);
 unsafe{assert!(NBR_ENTERED);assert!(!NBR_ACCEPT);assert!(!NBR_CHECKED);}
 assert_eq!(r,Err(Error::Parse));
 kani::cover!(true,"compact rejection returns Parse before any later scan step");
}
