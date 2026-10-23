#!/usr/bin/env python3
"""Actual full stage1 parent; explicit child contracts, scan cut only in GOTO.
Includes all data-Rc alias partitions of three arbitrary account buffers.
The resulting contextual check is conditional on the separately proved scan
and typed child contracts. It is not whole-stage SDK/owned equality by itself.
"""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/prefix-v7'
mode=sys.argv[2] if len(sys.argv)>2 else 'full';assert mode in ['full','alias','clean'];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s=(E/'src/lib.rs').read_text().replace('// Prefix certificate: argument assertions above occur before this return.\n  Err(())','if p.fail==4 {Err(())}else{Ok(vec![p.output;p.output_len])}')
s=s.replace('fn actual_sdk_stage1_prefix_binding()', 'fn actual_sdk_stage1_full_context()')
s=s.replace('let mut proof:[u8;688+PROOF]=kani::any();proof[..688].copy_from_slice(&candidate);proof[696]=2;','let mut proof:[u8;688+PROOF]=kani::any();')
s=s.replace('let mut checkpoint=[0u8;CP];','let mut checkpoint:[u8;CP]=kani::any();')
s=s.replace('let before=checkpoint[observed];','')
s=s.replace('let accounts=[a0,a1,a2];','''let cells=[a0.data.clone(),a1.data.clone(),a2.data.clone()];
 let mut accounts=[a0,a1,a2];
 let a:usize=kani::any();let b:usize=kani::any();let c:usize=kani::any();
 kani::assume(a<3 && b<3 && c<3);
 accounts[0].data=cells[a].clone();accounts[1].data=cells[b].clone();accounts[2].data=cells[c].clone();
 // Capture actual selected SDK storage before introducing external guards.
 let before=accounts[2].try_borrow_data().unwrap()[observed];
 let rd0=accounts[0].try_borrow_data().unwrap();let rd1=accounts[1].try_borrow_data().unwrap();
 unsafe {PLAN=Some(Plan{public_ptr:rd1.as_ptr(),public_len:rd1.len(),proof_ptr:rd0.as_ptr(),..p});}
 drop(rd1);drop(rd0);''')
s=s.replace('Some(accounts[1].try_borrow_mut_data().unwrap())','accounts[1].try_borrow_mut_data().ok()')
s=s.replace('let data=[3,p.k as u8];','''let held_proof:Option<RefMut<'_,&mut [u8]>>=if kani::any(){accounts[0].try_borrow_mut_data().ok()}else{None};
 let data=[3,p.k as u8];''')
s=s.replace('drop(held_shared);drop(held_mut);','drop(held_shared);drop(held_mut);drop(held_proof);')
s=s.replace('assert!(result.is_err());assert_eq!(after[observed],before);','''if result.is_ok(){assert_eq!(unsafe{CALLS},1);assert_eq!(p.output_len,CP);assert_eq!(after[observed],p.output);}
 else {assert_eq!(after[observed],before);}''')
s=s.replace('kani::cover!(unsafe{CALLS}==1);','''kani::cover!(result.is_ok(),"successful whole parent");
 kani::cover!(unsafe{CALLS}==1 && result.is_err(),"child error");
 kani::cover!(a==b && result.is_ok(),"shared immutable inputs");
 kani::cover!(c==a && result.is_err(),"checkpoint alias rejection");''')
# `after` is an intentional live shared CP borrow. It may alias inputs in the
# error case, so release it before checking that every source guard was dropped.
s=s.replace(' assert!(accounts[0].try_borrow_mut_data().is_ok());\n assert!(accounts[1].try_borrow_mut_data().is_ok());\n drop(after);',' drop(after);\n assert!(accounts[0].try_borrow_mut_data().is_ok());\n assert!(accounts[1].try_borrow_mut_data().is_ok());\n ')
if mode=='alias':
 s=s.replace('if p.fail==1 {Err(ProgramError::InvalidAccountData)}else{','if bytes.len()!=1880 || p.fail==1 {Err(ProgramError::InvalidAccountData)}else{')
 s=s.replace('kani::assume(a<3 && b<3 && c<3);','kani::assume(a<3 && b<3 && c<3);kani::assume(a!=0 || b!=1 || c!=2);')
 a=s.index(' if result.is_ok(){');b=s.index(' drop(after);',a)
 s=s[:a]+""" assert!(result.is_err());assert_eq!(unsafe{CALLS},0);assert_eq!(after[observed],before);
 kani::cover!(a==b,"shared input storage rejected");
 kani::cover!(c==a,"checkpoint alias rejected");
"""+s[b:]
 s=s.replace('#[kani::unwind(1772)]','#[kani::unwind(4)]')
elif mode=='clean':
 s=s.replace('kani::assume(a<3 && b<3 && c<3);','kani::assume(a==0 && b==1 && c==2);')
 s=s.replace('let mut proof:[u8;688+PROOF]=kani::any();','let mut proof:[u8;688+PROOF]=kani::any();proof[..688].copy_from_slice(&candidate);proof[696]=2;')
 s=s.replace('kani::cover!(a==b && result.is_ok(),"shared immutable inputs");','').replace('kani::cover!(c==a && result.is_err(),"checkpoint alias rejection");','')
s=s.replace('actual_sdk_stage1_full_context','actual_sdk_stage1_'+mode+'_context')
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text((E/'Cargo.toml').read_text().replace('aspis-s126-sdk-prefix-boundary-v7','aspis-s126-sdk-'+mode+'-context-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',parent_sha256=hashlib.sha256((E/'src/lib.rs').read_bytes()).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,mode=mode,decoder_length_contract='S2OwnedDecoderLengthV1.actual_wrong_length and existing DecoderSuccess.decode_success' if mode=='alias' else None,children=['decoder','validator','encoder','verifier','error/log mapper'],domains='All bytes in 58295/1880/1768 buffers; all 27 data-Rc alias partitions; optional external checkpoint shared, public/proof exclusive borrows; two full statement variants; verifier output fill value arbitrary, length0or1768 (arbitrary-byte writeback checked separately). Account metadata valid; separate full prefix guard check supplies metadata/error paths. Generic arbitrary SDK input lengths not closed by this fixed-buffer context.'),indent=2)+'\n')
