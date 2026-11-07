"""Generate minimal exact-carrier controls; these are method tests, not row credit."""
from pathlib import Path
E=Path(__file__).resolve().parent
specs={
 'plain':('Result<Variant,Error>','Ok(Variant::S2)','true','assert_eq!(r,Ok(Variant::S2));',''),
 'unit':('Result<(),Error>','Ok(())','true','assert!(r.is_ok());',''),
 'box':('Result<Box<u8>,Error>','Ok(Box::new(7))','out.is_ok()','assert_eq!(r.unwrap().as_ref(),&7);',''),
 'ref':("core::cell::Ref<'a,u8>",'cell.borrow()','**out<=255','assert_eq!(*r,7);',"cell:&'a core::cell::RefCell<u8>,"),
 'refmut':("core::cell::RefMut<'a,u8>",'cell.borrow_mut()','**out<=255','assert_eq!(*r,7);',"cell:&'a core::cell::RefCell<u8>,")}
for shape,(ret,body,weak,assertion,cellarg) in specs.items():
 args='&cell,' if cellarg else ''
 init='let cell=core::cell::RefCell::new(7u8);' if cellarg else ''
 lifetime="<'a>" if cellarg else ''
 src=f'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::modifies()]
#[kani::ensures(|out| {weak})]
fn NMD_shape{lifetime}({cellarg}_frame:&mut u8)->{ret} {{{body}}}
#[kani::modifies()]
#[kani::ensures(|out| !({weak}))]
fn NMD_inverse_shape{lifetime}({cellarg}_frame:&mut u8)->{ret} {{{body}}}
#[kani::modifies()]
#[kani::ensures(|out| {weak})]
fn NMD_modifies_shape{lifetime}({cellarg}frame:&mut u8)->{ret} {{*frame=1;{body}}}
#[kani::proof_for_contract(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_contract() {{{init}let mut frame=0;NMD_shape({args}&mut frame);}}
#[kani::proof_for_contract(NMD_inverse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_inverse() {{{init}let mut frame=0;NMD_inverse_shape({args}&mut frame);}}
#[kani::proof_for_contract(NMD_modifies_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_modifies() {{{init}let mut frame=0;NMD_modifies_shape({args}&mut frame);}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_real() {{{init}let mut frame=0;let r=NMD_shape({args}&mut frame);{assertion}}}
#[kani::proof]
#[kani::stub_verified(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_unimplied() {{{init}let mut frame=0;let r=NMD_shape({args}&mut frame);{assertion}}}
'''
 # Ref/RefMut real-body tests use actual guard lifetimes. No mutable statics.
 if cellarg: src=src.replace('#[kani::modifies()]','#[kani::modifies(cell)]')
 (E/('NMD_shape_'+shape+'.rs')).write_text(src)
print('Generated five shape families; ProgramResult requires program-root module separately')
