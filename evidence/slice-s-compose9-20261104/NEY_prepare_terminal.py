"""Frozen1880-byte terminal caller; every child reply/error and field is arbitrary."""
from NEY_native_patch import E,frozen,helpers
from NEY_source_tools import calls
import sys,subprocess,json,difflib
sys.path.insert(0,str(E.parent/'slice-s-compose7-20261103'))
from NEU_bridge_checks import COMMON,PUBLIC
slot=int(sys.argv[1]);assert 0<=slot<26
mode=sys.argv[2];assert mode in ['positive','value','argument']
subprocess.run([sys.executable,str(E/'NEY_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p);name='decode_pool_v1_pair_forest_terminal_statement_v1';a=f.index('pub fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8],f:&mut Frame,')
for old,new in [('decode_terminal_common_boxed_v1','common'),('decode_transfer_statement_boxed_v1','transfer'),('decode_withdrawal_statement_boxed_v1','withdrawal'),('validate_pool_v1_pair_forest_terminal_statement_v1','validate')]:native=calls(native,old,new,'f')
if mode=='argument':native=native.replace('bytes[PAYMENT_STATEMENT_OFFSET..]','bytes[PAYMENT_STATEMENT_OFFSET+1..]')
fields=['s.transition_kind() as u64']+['s.common().'+x+' as u64' for x in COMMON]
for x in PUBLIC:fields.append('match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>public.'+x+' as u64,PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>public.'+x+' as u64}')
fields += ['match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>public.recipient_commitment[i].0 as u64,_=>0}','match s{PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>public.amount as u64,_=>0}','match s{PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>public.destination_token_account[j] as u64,_=>0}']
fields_all=fields
fields=[fields[slot]]
project='fn project(s:&PoolV1PairForestTerminalStatementV1,slot:usize,i:usize,j:usize,k:usize)->u64{match slot{'+','.join(str(i)+'=>'+x for i,x in enumerate(fields))+',_=>0}}'
base=helpers().replace('aspis_statement::','crate::')
body=base+'\n'+project+'''
struct Frame<'a>{bytes:&'a [u8;1880],c:Result<PoolV1PairForestTerminalCommonV1,PoolV1PairForestTerminalFormatErrorV1>,s:Result<PoolV1PairForestTerminalStatementV1,PoolV1PairForestTerminalFormatErrorV1>,v:Result<(),PoolV1PairForestTerminalFormatErrorV1>,calls:u8,common_place:*const PoolV1PairForestTerminalCommonV1,statement_place:*const PoolV1PairForestTerminalStatementV1}
fn common(bytes:&[u8],f:&mut Frame)->Result<Box<PoolV1PairForestTerminalCommonV1>,PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==0&&bytes.len()==1880&&core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr()));f.calls=1;f.c.map(|c|{let b=Box::new(c);f.common_place=&*b;b})}
fn payment(common:Box<PoolV1PairForestTerminalCommonV1>,bytes:&[u8],kind:u8,f:&mut Frame)->Result<Box<PoolV1PairForestTerminalStatementV1>,PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==1&&core::ptr::eq(&*common,f.common_place)&&bytes.len()==216&&core::ptr::eq(bytes.as_ptr(),f.bytes[1664..].as_ptr())&&kind==f.bytes[5]);f.calls=2;f.s.map(|s|{let b=Box::new(s);f.statement_place=&*b;b})}
fn transfer(common:Box<PoolV1PairForestTerminalCommonV1>,bytes:&[u8],f:&mut Frame)->Result<Box<PoolV1PairForestTerminalStatementV1>,PoolV1PairForestTerminalFormatErrorV1>{payment(common,bytes,PoolV1TransitionKind::PrivateTransfer as u8,f)}
fn withdrawal(common:Box<PoolV1PairForestTerminalCommonV1>,bytes:&[u8],f:&mut Frame)->Result<Box<PoolV1PairForestTerminalStatementV1>,PoolV1PairForestTerminalFormatErrorV1>{payment(common,bytes,PoolV1TransitionKind::Withdrawal as u8,f)}
fn validate(s:&PoolV1PairForestTerminalStatementV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{assert!(f.calls==2&&core::ptr::eq(s,f.statement_place));f.calls=3;f.v}
'''+native+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn terminal(){{let bytes:[u8;1880]=kani::any();let c=if kani::any(){{Ok(NEE_common())}}else{{Err(any_error())}};let s=if kani::any(){{Ok(NEE_statement())}}else{{Err(any_error())}};let v=if kani::any(){{Ok(())}}else{{Err(any_error())}};let mut f=Frame{{bytes:&bytes,c,s,v,calls:0,common_place:core::ptr::null(),statement_place:core::ptr::null()}};let slot:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(slot<{len(fields)}&&i<8&&j<32&&k<20);let result=native(&bytes,&mut f);
let header=if @MAGIC@{{Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}}else if bytes[4]!=POOL_V1_PAIR_FOREST_TERMINAL_VERSION{{Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)}}else if bytes[5]!=PoolV1TransitionKind::PrivateTransfer as u8&&bytes[5]!=PoolV1TransitionKind::Withdrawal as u8{{Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)}}else if bytes[6]!=POOL_V1_DIGEST_ENCODING_VERSION{{Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)}}else{{Ok(())}};
match header{{Err(e)=>{{assert!(f.calls==0);assert!(matches!(result,Err(x) if x==e));}},Ok(())=>match c{{Err(e)=>{{assert!(f.calls==1);assert!(matches!(result,Err(x) if x==e));}},Ok(_)=>match s{{Err(e)=>{{assert!(f.calls==2);assert!(matches!(result,Err(x) if x==e));}},Ok(expected)=>{{assert!(f.calls==3);match (result,v){{(Err(x),Err(e))=>assert!(x==e),(Ok(out),Ok(()))=>assert!(project(&out,slot,i,j,k)==project(&expected,slot,i,j,k){'^1' if mode=='value' else ''}),_=>assert!(false)}}}}}}}}}}}}
'''
if mode=='value' and slot>=23:
 variant='PrivateTransfer' if slot==23 else 'Withdrawal'
 body=body.replace('let v=if kani::any()',f'kani::assume(matches!(s,Ok(PoolV1PairForestTerminalStatementV1::{variant}{{..}})));let v=if kani::any()')
body=body.replace('@MAGIC@','||'.join(f'bytes[{i}]!=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC[{i}]' for i in range(4)))
h=f+'\n#[cfg(kani)]\n#[path="NEY_terminal.rs"]\nmod NEY_terminal;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEY_terminal.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEY_native_contracts.patch').write_text(patch)
(E/'NEY_TERMINAL_CURRENT.json').write_text(json.dumps(dict(mode=mode,full_child_Result=True,frozen_body=original,native=native,source=body,fields=fields,field_slot=slot,all_fields=fields_all,domain='all live1880-byte bodies; arbitrary complete child Results and one scalar/byte/word/frontier projection at arbitrary component index; other lengths handled by separate metadata gate',classification='ruling y actual common/payment Box inputs and validator pointer, full errors, returned record and ordered calls; no new allocation in caller'),indent=1))
