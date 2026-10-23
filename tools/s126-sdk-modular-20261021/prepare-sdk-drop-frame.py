#!/usr/bin/env python3
"""Check exactly the actual std guard Drop operation, with a counter-only frame.
No SDK or guard model is stubbed. The custom harness obtains a real guard from
the original SDK and covers the same full metadata/counter/Rc/view domain.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-live-contracts/sources'
out=Path(sys.argv[1]);mode=sys.argv[2];assert mode in ['shared','exclusive'];assert not out.exists();(out/'src').mkdir(parents=True)
base=E/f'sdk-live-{mode}-v1';s=(base/'src/lib.rs').read_text()
method='try_borrow_data' if mode=='shared' else 'try_borrow_mut_data'
guard='Ref' if mode=='shared' else 'RefMut'
allowed='unsafe{(*counter).get()}>0' if mode=='shared' else 'unsafe{(*counter).get()} == -1'
result='unsafe{(*counter).get()}==old(unsafe{(*counter).get()})-1' if mode=='shared' else 'unsafe{(*counter).get()}==0'
wrapper='''#[cfg(kani)]
#[kani::requires(std::mem::size_of_val(&guard)==2*std::mem::size_of::<usize>())]
#[kani::requires(unsafe{*(std::ptr::addr_of!(guard).cast::<usize>().add(1))}==counter as usize)]
#[kani::requires(ALLOWED)]
#[kani::modifies(counter.cast::<isize>())]
#[kani::ensures(|_| RESULT)]
fn finish_guard(guard:std::cell::GUARD<'_,&mut [u8]>,counter:*const Cell<isize>){drop(guard);}
'''.replace('ALLOWED',allowed).replace('RESULT',result).replace('GUARD',guard)
s=s.replace('#[cfg(kani)] mod proofs {',wrapper+'\n#[cfg(kani)] mod proofs {',1)
s=s.replace(f'#[kani::proof_for_contract(AccountInfo::{method})]','#[kani::proof_for_contract(finish_guard)]')
s=s.replace(' drop(result);',' match result {Ok(guard)=>finish_guard(guard,counter),Err(error)=>assert!(matches!(error,ProgramError::AccountBorrowFailed))};')
assert '#[kani::stub' not in s and 'finish_guard(guard,counter)' in s
(out/'src/lib.rs').write_text(s)
(out/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-drop-MODE-v1"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('MODE',mode))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',mode=mode,source_sha256=sha(out/'src/lib.rs'),base_source_sha256=sha(base/'src/lib.rs'),qualification=__doc__,contract=wrapper,domain='Original SDK and actual std Ref/RefMut Drop, one actual typed AccountInfo,10MiB/all view lengths, arbitrary bytes/metadata, every signed data/lamport borrow flag and nonzero usize Rc header. Method supplies live guard; contract requires its exact borrow-counter pointer and positive(shared)/-1(exclusive) live count. Only that counter may be written, exact decrement/reset checked.',remaining='Compose actual SDK acquisition postcondition and direct real-guard-model coupling before caller use. Guard types/layout, valid runtime heap embedding, complete native/owned source/child/oracle joins and successful stage1 transport remain explicit. No whole S2 or unrestricted TOTAL claim.'),indent=2)+'\n')
