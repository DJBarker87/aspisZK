"""Frozen decoder oracle cuts; safe Box identity under ruling (aa)."""
from pathlib import Path
import subprocess,sys,json,difflib,hashlib
from NEX_native_patch import E,frozen,helpers
sys.path.insert(0,str(E.parent/'slice-s-compose7-20261103'))
from NEU_bridge_checks import COMMON
family,mode=sys.argv[1:3];selected=int(sys.argv[3]) if len(sys.argv)>3 else None;assert family in ['common','lane','afterstate','snapshot'];assert mode in ['positive','value','allocation','argument','reply']
subprocess.run([sys.executable,str(E/'NEX_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/'+('pair_forest_terminal.rs' if family in ['common','lane'] else 'pair_tree_profile.rs')
f=frozen(p);names=dict(common='decode_terminal_common_boxed_v1',lane='decode_lane_transition_boxed_v1',afterstate='decode_pair_afterstate_boxed_v1',snapshot='decode_pair_live_snapshot_boxed_v1');name=names[family]
a=f.index('fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
# Full typed arbitrary records; all their scalars/arrays are unconstrained.
base=helpers().replace('aspis_statement::','crate::')
body=original.replace('fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8], f: &mut Frame,')
if family=='common':
 size=1880;ty='PoolV1PairForestTerminalCommonV1';err='PoolV1PairForestTerminalFormatErrorV1'
 body=body.replace('decode_digest_canonical(','digest(').replace('    )\n    .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest)?;', '    f)\n    .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest)?;').replace('decode_lane_transition_boxed_v1(&bytes[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET])','lane(&bytes[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET],f)')
 body=body.replace('Ok(Box::new(PoolV1PairForestTerminalCommonV1 {','let boxed=Box::new(PoolV1PairForestTerminalCommonV1 {').replace('    }))','    });\n    f.allocated=&*boxed;\n    Ok(boxed)')
 frame=f'''struct Frame<'a>{{bytes:&'a [u8;1880],digest:Result<Digest,()>,lane:Result<PoolV1PairLatePublicStatementV1,{err}>,calls:u8,allocated:*const {ty}}}
fn digest(bytes:&[u8;32],f:&mut Frame)->Result<Digest,()>{{assert!(f.calls==0);let j:usize=kani::any();kani::assume(j<32);assert!(bytes[j]==f.bytes[112+j]);f.calls=1;f.digest}}
fn lane(bytes:&[u8],f:&mut Frame)->Result<Box<PoolV1PairLatePublicStatementV1>,{err}>{{assert!(f.calls==1&&bytes.len()==1520&&core::ptr::eq(bytes.as_ptr(),f.bytes[144..].as_ptr()));f.calls=2;f.lane.map(Box::new)}}
'''
 init='let c=NEE_common();let d=if kani::any(){Ok(NEE_digest())}else{Err(())};let reply=if kani::any(){Ok(c.lane_transition)}else{Err(any_error())};let mut f=Frame{bytes:&bytes,digest:d,lane:reply,calls:0,allocated:core::ptr::null()};'
 fields=['master_account[j] as u64','checkpoint_account[j] as u64','selected_lane_account[j] as u64','output_lane as u64','checkpoint_sequence','historical_global_anchor[i].0 as u64']+[x.replace('lane_transition.','lane_transition.')+' as u64' for x in COMMON[6:]]
 left='match slot{'+','.join(str(i)+'=>out.'+x for i,x in enumerate(fields))+',_=>0}'
 expected=['bytes[8+j] as u64','bytes[40+j] as u64','bytes[72+j] as u64','bytes[7] as u64','u64::from_le_bytes(bytes[104..112].try_into().unwrap())','d.unwrap()[i].0 as u64']+['c.'+x for x in fields[6:]]
 right='match slot{'+','.join(str(i)+'=>'+x for i,x in enumerate(expected))+',_=>0}'
 check=f'''match d{{Err(_)=>{{assert!(f.calls==1);assert!(matches!(actual,Err({err}::NonCanonicalDigest)));assert!(f.allocated.is_null());}},Ok(_)=>match reply{{Err(e)=>{{assert!(f.calls==2);assert!(matches!(actual,Err(x) if x==e));assert!(f.allocated.is_null());}},Ok(_)=>{{assert!(f.calls==2);let out=actual.unwrap();assert!(core::ptr::eq(&*out,f.allocated));assert!(({left})==({right}));assert!(!core::ptr::eq((&*out) as *const _ as *const u8,bytes.as_ptr()));}}}}}}'''
else:
 size={'lane':1520,'afterstate':688,'snapshot':800}[family]
 ty={'lane':'PoolV1PairLatePublicStatementV1','afterstate':'PoolV1PairVerifiedAfterstateV1','snapshot':'PoolV1PairLiveSnapshotV1'}[family]
 err='PoolV1PairForestTerminalFormatErrorV1' if family=='lane' else 'PoolV1PairLatePublicStatementErrorV1'
 child={'lane':'decode_pool_v1_pair_late_public_statement_boxed_v1','afterstate':'decode_pool_v1_pair_verified_afterstate_v1','snapshot':'decode_pool_v1_pair_live_snapshot_v1'}[family]
 childErr={'lane':'PoolV1PairLatePublicStatementErrorV1','afterstate':'PoolV1PairVerifierTransportErrorV1','snapshot':'PoolV1PairLiveSnapshotErrorV1'}[family]
 body=body.replace(child+'(bytes)','child(bytes,f)')
 if family!='lane':
  body=body.replace('Ok(Box::new(','let boxed=Box::new(').replace('    ))','    );\n    f.allocated=&*boxed;\n    Ok(boxed)')
 frame=f'''struct Frame<'a>{{bytes:&'a [u8;{size}],reply:Result<{ty},{childErr}>,calls:u8,allocated:*const {ty}}}
fn child(bytes:&[u8],f:&mut Frame)->Result<{'Box<'+ty+'>' if family=='lane' else ty},{childErr}>{{assert!(f.calls==0&&bytes.len()=={size}&&core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr()));f.calls=1;REPLY}}
'''
 frame=frame.replace('REPLY','f.reply.map(|v|{let b=Box::new(v);f.allocated=&*b;b})' if family=='lane' else 'f.reply')
 v='c.lane_transition'+('.candidate_afterstate' if family=='afterstate' else '.live_snapshot' if family=='snapshot' else '')
 init=f'let c=NEE_common();let reply=if kani::any(){{Ok({v})}}else{{Err(NEE_any_{childErr}())}};let mut f=Frame{{bytes:&bytes,reply,calls:0,allocated:core::ptr::null()}};'
 subset=COMMON[6:] if family=='lane' else COMMON[12:] if family=='afterstate' else COMMON[6:12]
 prefix='lane_transition.'+('candidate_afterstate.' if family=='afterstate' else 'live_snapshot.' if family=='snapshot' else '')
 fields=[x.removeprefix(prefix)+' as u64' for x in subset];left='match slot{'+','.join(str(i)+'=>out.'+x for i,x in enumerate(fields))+',_=>0}';right=left.replace('out.','expected.')
 variant={'lane':'LaneTransition','afterstate':'Afterstate','snapshot':'Snapshot'}[family]
 check=f'''assert!(f.calls==1);match (actual,reply){{(Ok(out),Ok(expected))=>{{assert!(core::ptr::eq(&*out,f.allocated));assert!(({left})==({right}));assert!(!core::ptr::eq((&*out) as *const _ as *const u8,bytes.as_ptr()));}},(Err({err}::{variant}(e)),Err(expected))=>assert!(e==expected),_=>assert!(false)}}'''
if mode=='value':check=check.replace('==('+right+')','==(('+right+')^1)')
if mode=='allocation':
 body=body.replace('Ok(boxed)','Ok(Box::new(*boxed))') if family!='lane' else body.replace('.map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)','.map(|b|Box::new(*b)).map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)')
if mode=='argument':body=body.replace('child(bytes,f)','child(&bytes[1..],f)').replace('lane(&bytes[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET],f)','lane(&bytes[LATE_STATEMENT_OFFSET+1..PAYMENT_STATEMENT_OFFSET],f)')
if mode=='reply':frame=frame.replace('f.reply','Err(NEE_any_'+childErr+'())') if family!='common' else frame.replace('f.digest','Err(())')
# Add direct local pointer observations only; no mutable static or unsafe carrier.
code=base+'\n'+frame+'\n'+body+f'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn decoder(){{let bytes:[u8;{size}]=kani::any();{init}let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let slot:usize=kani::any();kani::assume(i<8&&j<32&&k<20&&slot<{len(fields)});let actual=native(&bytes,&mut f);{check}}}
'''
if selected is not None:
 assert 0<=selected<len(fields)
 code=code.replace('let slot:usize=kani::any();',f'let slot:usize={selected};')
hook=f+'\n#[cfg(kani)]\n#[path="NEX_decoder.rs"]\nmod NEX_decoder;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/'+p.rsplit('/',1)[0]+'/NEX_decoder.rs\n@@ -0,0 +1,'+str(len(code.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in code.splitlines())
(E/'NEX_native_contracts.patch').write_text(patch)
(E/'NEX_DECODER_CURRENT.json').write_text(json.dumps(dict(family=family,mode=mode,selected=selected,function=p+'::'+name,frozen_body=original,native=body,fields=fields,size=size,source=code,classification='ruling y exact borrowed slice/full arbitrary Result/local ordered log; aa safe Box value and same allocated pointer; arbitrary complete-record projection'),indent=1))
