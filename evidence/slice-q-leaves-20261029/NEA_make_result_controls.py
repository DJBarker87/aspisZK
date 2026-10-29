from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NEA_payload import save
p=json.loads((E/'NEA_PAYLOAD.json').read_text());k='crates/aspis-core/src/r0/domain.rs';s=p[k]
s=s.replace('kani::ensures(|r| match r {Ok(v)=>index < $bound && v.0==index,Err(e)=>index >= $bound && *e==Error::IndexOutOfRange})','kani::ensures(|r| (match r {Ok(v)=>index < $bound && v.0==index,Err(e)=>index >= $bound && *e==Error::IndexOutOfRange}) != cfg!(NEA_wrong_index))')
s+='''
#[cfg(kani)] mod NEA_result_controls {use super::*;
#[kani::requires(i<FIBRE_COUNT)]
#[kani::ensures(|r| r.is_ok() != cfg!(NEA_wrong_weak))]
fn weak(i:usize)->Result<FibreIndex,Error>{FibreIndex::new(i)}
#[kani::proof_for_contract(weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]
fn weak_contract(){let i:usize=kani::any();kani::assume(i<FIBRE_COUNT);let _=weak(i);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]
fn real_caller(){let i:usize=kani::any();kani::assume(i<FIBRE_COUNT);let v=weak(i).unwrap();assert!(v.get()==i);}
#[kani::proof]
#[kani::stub_verified(weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]
fn replacement_caller(){let i:usize=kani::any();kani::assume(i<FIBRE_COUNT);let v=weak(i).unwrap();assert!(v.get()==i);}
#[kani::requires(i<FIBRE_COUNT)]
#[kani::modifies(&raw mut b[0])]
#[kani::ensures(|r| r.is_ok())]
fn frame(b:&mut[usize;2],i:usize)->Result<FibreIndex,Error>{if cfg!(NEA_wrong_frame){b[1]=i;}else{b[0]=i;}FibreIndex::new(i)}
#[kani::proof_for_contract(frame)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]
fn frame_contract(){let i:usize=kani::any();kani::assume(i<FIBRE_COUNT);let mut b:[usize;2]=kani::any();let _=frame(&mut b,i);}
}
'''
# The actual constructor proof uses the official copy replacement too.
s=s.replace('#[kani::proof_for_contract(FibreIndex::new)] fn constructor()', '#[kani::proof_for_contract(FibreIndex::new)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)] fn constructor()')
p[k]=s;save(p)
