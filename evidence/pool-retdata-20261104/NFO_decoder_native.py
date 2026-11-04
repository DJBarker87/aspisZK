"""Exact frozen ASR8 decoder cut with three local-record pure child oracles."""
from pathlib import Path
import subprocess,re,json,difflib,sys
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode=sys.argv[1] if len(sys.argv)>1 else 'positive'
assert mode in ['positive','digest-arg','after-arg','validator-arg','reply','digest-error','after-error','validation-error','input-frame']
get=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
rust=get('crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs')
def function(name):
 a=re.search(r'(?m)^(?:pub )?fn '+re.escape(name)+r'\(',rust).start();a=rust.index('fn ',a);b=rust.index('{',a);depth=1;c=b+1
 while depth:depth+=(rust[c]=='{')-(rust[c]=='}');c+=1
 return rust[a:c]
body=function('decode_pool_v1_pair_forest_terminal_result_v1');body=body[body.index('{')+1:-1]
for child,new in [('decode_digest_canonical','digest'),('decode_pool_v1_pair_verified_afterstate_v1','after'),('validate_result','validate')]:
 pos=body.index(child+'(');a=pos+len(child);depth=1;b=a+1
 while depth:depth+=(body[b]=='(')-(body[b]==')');b+=1
 body=body[:pos]+new+body[a:b-1].rstrip().rstrip(',')+',frame)'+body[b:]
# Native error and arbitrary carrier factories from already committed NFO reader.
src=json.loads((E/'NFO_K007-shape.json').read_text())['source'];helpers=src[src.index('fn digest()'):src.index('struct Runtime {')]
helpers=helpers.replace('fn digest()', 'fn any_digest()').replace('digest()', 'any_digest()')
# The first replace also affects the spelling once; normalize it.
helpers=helpers.replace('any_any_digest','any_digest')
constants='\n'.join(re.findall(r'(?m)^const RESULT_\w+_OFFSET[^;]+;',rust))+'\n'
atomic='fn atomic_error()->aspis_statement::AtomicStatementError{match kani::any::<u8>(){0=>aspis_statement::AtomicStatementError::NonCanonicalDigest,1=>aspis_statement::AtomicStatementError::NonCanonicalAssetId,2=>aspis_statement::AtomicStatementError::FeeOutOfRange,3=>aspis_statement::AtomicStatementError::PathDepthMismatch,4=>aspis_statement::AtomicStatementError::InsertionIndexOutOfRange,5=>aspis_statement::AtomicStatementError::CurrentAnchorMismatch,_=>aspis_statement::AtomicStatementError::OutputAnchorMismatch}}\n'
source=atomic+constants+'use super::*;\nuse aspis_statement::pool_v1::*;\nuse aspis_core::field::M31;\n'+helpers+'\n'+function('transition_kind')+r'''
struct Frame<'a>{bytes:&'a [u8;792],calls:u8,dok:bool,aok:bool,vok:bool,digest:aspis_statement::Digest,
 after:PoolV1PairVerifiedAfterstateV1,ae:PoolV1PairVerifierTransportErrorV1,ve:PoolV1PairForestTerminalFormatErrorV1,
 expected:PoolV1PairForestTerminalResultV1,family:u8,row:usize,word:usize,index:usize,byte:usize}
fn digest(a:&[u8;32],f:&mut Frame)->Result<aspis_statement::Digest,aspis_statement::AtomicStatementError>{
 assert!(f.calls==0&&a[f.index]==f.bytes[72+f.index]);f.calls=1;
 if f.dok{Ok(f.digest)}else{Err(atomic_error())}}
fn after(a:&[u8],f:&mut Frame)->Result<PoolV1PairVerifiedAfterstateV1,PoolV1PairVerifierTransportErrorV1>{
 assert!(f.calls==1&&a.len()==688&&core::ptr::eq(a.as_ptr(),unsafe{f.bytes.as_ptr().add(104)})&&a[f.byte]==f.bytes[104+f.byte]);f.calls=2;
 if f.aok{Ok(f.after)}else{Err(f.ae)}}
fn validate(a:&PoolV1PairForestTerminalResultV1,f:&mut Frame)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{
 assert!(f.calls==2&&observe(a,f.family,f.row,f.word,f.index)==observe(&f.expected,f.family,f.row,f.word,f.index));f.calls=3;
 if f.vok{Ok(())}else{Err(f.ve)}}
fn native(bytes:&[u8],frame:&mut Frame)->Result<PoolV1PairForestTerminalResultV1,PoolV1PairForestTerminalFormatErrorV1>{
'''+body+r'''
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
fn association(){
 let bytes:[u8;792]=kani::any();let initial:usize=kani::any();kani::assume(initial<792);let original=bytes[initial];
 let family:u8=kani::any();kani::assume(family<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let index:usize=kani::any();kani::assume(index<32);let byte:usize=kani::any();kani::assume(byte<688);
 let mut master=[0u8;32];master[index]=bytes[8+index];let mut selected=[0u8;32];selected[index]=bytes[40+index];
 let digest=any_digest();let a=result().verified_afterstate;
 let kind=if bytes[5]==1{PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};
 let expected=PoolV1PairForestTerminalResultV1{transition_kind:kind,master_account:master,selected_lane_account:selected,output_lane:bytes[7],nullifier:digest,verified_afterstate:a};
 let mut f=Frame{bytes:&bytes,calls:0,dok:kani::any(),aok:kani::any(),vok:kani::any(),digest,after:a,ae:NFO_any_PoolV1PairVerifierTransportErrorV1(),ve:any_error(),expected,family,row,word,index,byte};
 let actual=native(&bytes,&mut f);
 if bytes[..4]!=POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC {assert!(f.calls==0&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)));}
 else if bytes[4]!=1 {assert!(f.calls==0&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)));}
 else if bytes[5]!=1&&bytes[5]!=2 {assert!(f.calls==0&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)));}
 else if bytes[6]!=1 {assert!(f.calls==0&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)));}
 else if !f.dok{assert!(f.calls==1&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest)));}
 else if !f.aok{assert!(f.calls==2&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::Afterstate(e)) if e==f.ae));}
 else if !f.vok{assert!(f.calls==3&&matches!(actual,Err(e) if e==f.ve));}
 else{let r=actual.unwrap();assert!(f.calls==3&&observe(&r,family,row,word,index)==observe(&expected,family,row,word,index));}
 assert!(bytes[initial]==original);
}
'''
if mode=='digest-arg':source=source.replace('a[f.index]==f.bytes[72+f.index]','a[f.index]==f.bytes[73+f.index]')
if mode=='after-arg':source=source.replace('add(104)','add(103)')
if mode=='validator-arg':source=source.replace('validate(&result,frame)','validate(&{let mut r=result;r.output_lane^=1;r},frame)')
if mode=='reply':source=source.replace('Ok(result)','Ok({let mut r=result;r.output_lane^=1;r})')
if mode=='digest-error':source=source.replace('.map_err(|_| PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest)?','.map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongVersion)?')
if mode=='after-error':source=source.replace('.map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Afterstate(error))?','.map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongVersion)?')
if mode=='validation-error':source=source.replace('validate(&result,frame)?','let _=validate(&result,frame);')
if mode=='input-frame':source=source.replace('bytes[initial]==original','bytes[initial]!=original')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=get(p)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFO_native.patch').write_text(patch);(E/'NFO_CURRENT.json').write_text(json.dumps(dict(mode='decoder-'+mode,source=source,source_body=body,classification='source-exact native decoder cut, canonical child bridges reused; arbitrary792 bytes and full child Result replies'),indent=1)+'\n')
