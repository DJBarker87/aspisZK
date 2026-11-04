"""Valid216 child/Box association, one arbitrary complete-record projection."""
from pathlib import Path
import subprocess,sys,json,difflib
from NEU_native_patch import E,frozen,helpers
from NEU_bridge_checks import COMMON,PUBLIC
branch,mode=sys.argv[1:];assert branch in ['transfer','withdrawal'];assert mode in ['positive','negative','wrong_input','wrong_reply']
subprocess.run([sys.executable,str(E/'NEU_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p);name='decode_'+branch+'_statement_boxed_v1';a=f.index('fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
variant='PrivateTransfer' if branch=='transfer' else 'Withdrawal';ty='PoolV1PrivateTransferPublicV1' if branch=='transfer' else 'PoolV1WithdrawalPublicV1'
fields=['common.'+x for x in COMMON]+['public.'+x for x in PUBLIC+(['recipient_commitment[i].0'] if branch=='transfer' else ['amount','destination_token_account[j]'])]
left='match slot{'+','.join(str(i)+'=>'+x+' as u64' for i,x in enumerate(fields))+',_=>0}'
right=left.replace('common.','expected_common.').replace('public.','expected_public.')
if mode=='negative':right=right.replace('expected_common.master_account[j] as u64','expected_common.master_account[j] as u64^1')
native=original.replace('fn '+name+'(','fn native(').replace(') -> Result<Box<PoolV1PairForestTerminalStatementV1>, PoolV1PairForestTerminalFormatErrorV1> {',',f:&mut Frame) -> Result<Box<PoolV1PairForestTerminalStatementV1>, PoolV1PairForestTerminalFormatErrorV1> {').replace('\n,f:&mut Frame)','\nf:&mut Frame)').replace('decode_pool_v1_'+('private_transfer' if branch=='transfer' else 'withdrawal')+'_public_v1(payment)','decode(payment,f)')
body=helpers().replace('aspis_statement::','crate::')+f'''
struct Frame<'a>{{bytes:&'a [u8;216],reply:Result<{ty},PoolV1PaymentStatementFormatError>,calls:u8}}
fn decode(bytes:&[u8],f:&mut Frame)->Result<{ty},PoolV1PaymentStatementFormatError>{{assert!(f.calls==0&&bytes.len()==216&&core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr()));f.calls=1;f.reply}}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn box_decode_window(){{let common=NEE_common();let s=NEE_statement();let public=match s{{PoolV1PairForestTerminalStatementV1::{variant}{{public,..}}=>public,_=>{{kani::assume(false);unreachable!()}}}};let bytes:[u8;216]=kani::any();let reply=if kani::any(){{Ok(public)}}else{{Err(NEE_any_PoolV1PaymentStatementFormatError())}};let mut f=Frame{{bytes:&bytes,reply,calls:0}};let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let slot:usize=kani::any();kani::assume(i<8&&j<32&&k<20&&slot<{len(fields)});let actual=native(Box::new(common),&bytes,&mut f);assert!(f.calls==1);match (actual,reply){{(Ok(out),Ok(expected_public))=>match out.as_ref(){{PoolV1PairForestTerminalStatementV1::{variant}{{common,public}}=>{{let expected_common=&common_expected(common,&common);}},_=>assert!(false)}},(Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e)),Err(expected))=>assert!(e==expected),_=>assert!(false)}}}}
'''
# Keep the original expected common outside the matched out/common binding.
body=body.replace('let actual=native(Box::new(common),&bytes,&mut f);','let expected_common=common;let actual=native(Box::new(common),&bytes,&mut f);').replace('let expected_common=&common_expected(common,&common);','assert!(('+left+')==('+right+'));')
if mode=='wrong_input':body=body.replace('decode(payment,f)','decode(&payment[1..],f)')
if mode=='wrong_reply':body=body.replace('f.calls=1;f.reply','f.calls=1;Err(PoolV1PaymentStatementFormatError::WrongMagic)')
changed=f+'\n#[cfg(kani)]\n#[path="NEU_box_decode.rs"]\nmod NEU_box_decode;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEU_box_decode.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEU_native_contracts.patch').write_text(patch)
(E/'NEU_BOX_DECODE_CURRENT.json').write_text(json.dumps(dict(branch=branch,mode=mode,frozen_body=original,native=native,fields=fields,domain='every typed common, arbitrary live216 bytes and complete arbitrary typed public/error reply; arbitrary field/byte/word/frontier index',classification='ruling y immutable child reply, full Box field projection and error mapping; no whole-buffer comparison or arbitrary-byte transmute'),indent=1)+'\n')
