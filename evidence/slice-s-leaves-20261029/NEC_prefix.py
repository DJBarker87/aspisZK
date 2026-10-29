"""Actual frozen entry-to-first-child windows. These are explicitly not closures."""
import subprocess,os
R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',R+':'+p],text=True)
def files(kind):
 terminal='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
 tree='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
 adapter='programs/r1-cost-probe/src/r1_pool_adapter.rs'
 C='PoolV1PairForestTerminalCommonV1';S='PoolV1PairForestTerminalStatementV1';F='PoolV1PairForestTerminalFormatErrorV1'
 L='PoolV1PairLatePublicStatementV1';LE='PoolV1PairLatePublicStatementErrorV1';V='crate::pool_v1::PoolV1PairLiveSnapshotV1'
 P='PoolV1PrivateTransferPublicV1';W='PoolV1WithdrawalPublicV1';PE='PoolV1PaymentStatementFormatError'
 # path, function, bytes, offset, child width, callbacks, owned argument, header
 specs={
 'lane':(terminal,'decode_lane_transition_boxed_v1','1520',0,1520,[('super::decode_pool_v1_pair_late_public_statement_boxed_v1','Box<'+L+'>',LE,'&[u8]')],False,[]),
 'common':(terminal,'decode_terminal_common_boxed_v1','1880',112,32,[('crate::atomic_statement::decode_digest_canonical','crate::poseidon2::Digest','crate::atomic_statement::AtomicStatementError','&[u8;32]')],False,[]),
 'transfer':(terminal,'decode_transfer_statement_boxed_v1','216',0,216,[('super::decode_pool_v1_private_transfer_public_v1',P,PE,'&[u8]')],True,[]),
 'withdrawal':(terminal,'decode_withdrawal_statement_boxed_v1','216',0,216,[('super::decode_pool_v1_withdrawal_public_v1',W,PE,'&[u8]')],True,[]),
 'statement':(terminal,'decode_pool_v1_pair_forest_terminal_statement_v1','1880',0,1880,[('super::decode_terminal_common_boxed_v1','Box<'+C+'>',F,'&[u8]')],False,list(b'ASF8')+[1,None,1,None]),
 'request':(terminal,'decode_pool_v1_pair_forest_terminal_request_v1','320',104,216,[('super::decode_pool_v1_private_transfer_public_v1',P,PE,'&[u8]'),('super::decode_pool_v1_withdrawal_public_v1',W,PE,'&[u8]')],False,list(b'ASQ8')+[1,None,1,0]),
 'late':(tree,'decode_pool_v1_pair_late_public_statement_boxed_v1','1520',32,800,[('super::decode_pair_live_snapshot_boxed_v1','Box<'+V+'>',LE,'&[u8]')],False,list(b'ASPLATE1')+[1,2,32,0,32,3,0,0,176,2,0,0,240,5,0,0]+[0]*8),
 'public':(adapter,'decode_public_statement_box','1880',0,1880,[('aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1',S,F,'&[u8]')],False,[]),
 'scan':(adapter,'scan_proof_buffer','{verifier::PROOF_BYTES+688}',0,688,[('aspis_statement::pool_v1::decode_pool_v1_pair_verified_afterstate_v1','aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1','aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1','&[u8]')],False,[])
 }
 path,name,n,offset,width,callbacks,owned,header=specs[kind]
 v=frozen(path)
 argname='payment' if owned else 'bytes'
 v=v.replace(('pub(crate) fn ' if kind=='late' else 'pub fn ' if kind in ['statement','request'] else 'fn ')+name+'(', '#[cfg_attr(kani,kani::requires(NEC_prefix::domain('+argname+')))]\n#[cfg_attr(kani,kani::ensures(|_| false))]\n#[cfg_attr(kani,kani::modifies())]\n'+('pub(crate) fn ' if kind=='late' else 'pub fn ' if kind in ['statement','request'] else 'fn ')+name+'(',1)
 stem=path.rsplit('/',1)[0];v+='\n#[cfg(kani)]#[path="NEC_prefix.rs"]mod NEC_prefix;\n'
 text='use super::*;\nuse alloc::boxed::Box;\n'
 if path==adapter:text+='use aspis_statement::pool_v1::*;\n'
 text+='static mut BASE:usize=0;\n'
 conditions=[f'bytes.len()=={n}']+[f'bytes[{i}]=={x}' for i,x in enumerate(header) if x is not None]
 if kind in ['statement','request']:conditions+=['(bytes[5]==1 || bytes[5]==2)']
 if kind=='request' and os.environ.get('NEC_PREFIX_KIND'):conditions+=["bytes[5]=="+os.environ['NEC_PREFIX_KIND']]
 text+='pub fn domain(bytes:&[u8])->bool {'+' && '.join(conditions)+'}\n'
 neg='true' if os.environ.get('NEC_INVERT') else 'false'
 text+=f'fn observe(bytes:&[u8]){{assert!((bytes.as_ptr() as usize==unsafe{{BASE}}+{offset} && bytes.len()=={width}) != {neg},"NEC_prefix_same_input");kani::cover!(true,"NEC_prefix_reached");kani::assume(false);}}\n'
 for i,(target,ret,err,arg) in enumerate(callbacks):text+=f'fn child{i}(bytes:{arg})->Result<{ret},{err}>{{observe(bytes);unreachable!()}}\n'
 text+=f'#[kani::proof_for_contract(super::{name})]\n'
 for i,(target,*_) in enumerate(callbacks):text+=f'#[kani::stub({target},child{i})]\n'
 text+='#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEC_kmx::KMX_copy_nonoverlapping)]\n#[kani::unwind(34)]\nfn prefix_contract(){\n'
 text+=f'let mut bytes:[u8;{n}]=kani::any();\n'
 for i,x in enumerate(header):
  if x is not None:text+=f'bytes[{i}]={x};\n'
 if kind in ['statement','request']:text+='bytes[5]='+os.environ.get('NEC_PREFIX_KIND','if kani::any(){1}else{2}')+';\n'
 text+='unsafe{BASE=bytes.as_ptr() as usize;}\n'
 if owned:
  text+=f'let common:{C}=unsafe{{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<{C}>()]>() )}};\n'
  text+=f'let _=super::{name}(Box::new(common),&bytes);\n'
 else:text+=f'let _=super::{name}(&bytes);\n'
 text+='}\n'
 out={path:v,stem+'/NEC_prefix.rs':text}
 if path==adapter:
  lib='programs/r1-cost-probe/src/lib.rs';out[lib]='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen(lib)+'\n#[cfg(kani)]mod NEC_kmx {extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));}\n'
 return out
