"""Thin immutable-slice forwarding root and safe Box ownership, ruling(y)/(aa)."""
from NEY_native_patch import E,frozen,helpers,program
from NEY_source_tools import calls
import sys,subprocess,json
slot=int(sys.argv[1]);assert 0<=slot<26
mode=sys.argv[2];assert mode in ['positive','value','reply','allocation']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=frozen(p);name='decode_public_statement_box';a=f.index('fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
assert 'bytes[' not in original and '.len()' not in original
native=original.replace('fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8],f:&mut Frame,')
native=calls(native,'decode_pool_v1_pair_forest_terminal_statement_v1','decode','f')
native=native.replace('Ok(Box::new(','let out=Box::new(').replace('    ))','    );\n    f.allocated=&*out;\n    Ok(out)')
if mode=='allocation':native=native.replace('Ok(out)','Ok(Box::new(*out))')
terminal=json.loads((E.parent/'slice-s-compose8-20261104/NEX_K133-shape.json').read_text());project=terminal['source'].split('fn project(',1)[1].split('\nstruct Frame',1)[0];project='fn project(s:&PoolV1PairForestTerminalStatementV1,slot:usize,i:usize,j:usize,k:usize)->u64{'+terminal['fields'][slot]+'}'
body=helpers()+'\n'+project+'''
struct Frame<'a>{bytes:&'a [u8],reply:Result<PoolV1PairForestTerminalStatementV1,PoolV1PairForestTerminalFormatErrorV1>,calls:u8,allocated:*const PoolV1PairForestTerminalStatementV1}
fn decode(bytes:&[u8],f:&mut Frame)->Result<PoolV1PairForestTerminalStatementV1,PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==0&&bytes.len()==f.bytes.len()&&core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr()));f.calls=1;f.reply}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEY_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NEY_KMX::KMX_copy_from_slice)]
fn public(){{let bytes:[u8;1880]=kani::any();let reply=if kani::any(){{Ok(NEE_statement())}}else{{Err(any_error())}};let mut f=Frame{{bytes:&bytes,reply,calls:0,allocated:core::ptr::null()}};let slot:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(slot<{len(terminal['fields'])}&&i<8&&j<32&&k<20);let result=native(&bytes,&mut f);assert!(f.calls==1);match (result,reply){{(Ok(out),Ok(expected))=>{{assert!(core::ptr::eq(&*out,f.allocated));assert!(project(&out,slot,i,j,k)==project(&expected,slot,i,j,k){'^1' if mode=='value' else ''});assert!(!core::ptr::eq((&*out) as *const _ as *const u8,bytes.as_ptr()));}},(Err(ProgramError::InvalidAccountData),Err(_))=>assert!(f.allocated.is_null()),_=>assert!(false)}}}}
'''
if mode=='reply':body=body.replace('f.calls=1;f.reply','f.calls=1;f.reply.map(|mut s|{match &mut s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,..}|PoolV1PairForestTerminalStatementV1::Withdrawal{common,..}=>common.master_account[0]^=1};s})')
program(body,'NEY_public')
(E/'NEY_PUBLIC_CURRENT.json').write_text(json.dumps(dict(mode=mode,full_child_Result=True,frozen_body=original,native=native,source=body,fields=[terminal['fields'][slot]],field_slot=slot,domain='all valid immutable live slices; no root size or byte restriction; full child Result including every format error and one returned field at arbitrary component index',classification='source-checked immutable Slice forwarding identity, no input inspection/length branch, native full typed child Result and aa Box value/same allocation/error frame; slot indices are universal observation coordinates, not input preconditions',input_projection='physical immutable Slice ABI/identity and exact source call expression; no buffer representation change'),indent=1))
