from pathlib import Path
from NEC_templates import template
import subprocess,os,difflib,re,json,hashlib
E=Path(__file__).resolve().parent;R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 def frozen(n):return subprocess.check_output(['git','show',R+':'+n],text=True)
 from NEC_arbitrary import additions
 out=additions()
 n='crates/aspis-statement/src/lib.rs'
 out[n]='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen(n)+'\n#[cfg(kani)] mod NEC_kmx { extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n'
 out['crates/aspis-statement/src/pool_v1/NEC_decode.rs']=template('NEC_decode').replace('if kani::any(){let x:',('if false{let x:' if os.environ.get('NEC_BRANCH')=='error' else 'if true{let x:' if os.environ.get('NEC_BRANCH')=='success' else 'if kani::any(){let x:')).replace('NEC_OBLIGATION',os.environ.get('NEC_OBLIGATION','same && calls')).replace('NEC_GROUP',os.environ.get('NEC_GROUP','0')).replace('NEC_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false')
 out['crates/aspis-statement/src/pool_v1/NEC_reference.rs']=template('NEC_reference')
 if os.environ.get('NEC_PURE_VALUE'):
  n='crates/aspis-statement/src/pool_v1/NEC_decode.rs';v=out[n]
  v=v.replace('fn after_child(bytes:&[u8])->Result<After,AfterError>{', 'fn after_child(bytes:&[u8])->Result<After,AfterError>{\n let x:After=kani::any();kani::assume(after_word(&x)==unsafe{WORD});return Ok(x);')
  # Remove unreachable old observer body (no runtime effect, no ghost writes).
  start=v.index('\n unsafe{CALLS=',v.index('fn after_child'))
  end=v.index('\nfn live_child',start)
  v=v[:start]+'\n}'+v[end:]
  v=v.replace('WORD=0;AFTER_ERROR=None;LIVE_ERROR=None;', 'WORD=kani::any();AFTER_ERROR=None;LIVE_ERROR=None;')
  start=v.index('pub fn post_after(');end=v.index('\npub fn post_live',start)
  v=v[:start]+'''pub fn post_after(result:&Result<Box<After>,LateError>,_bytes:&[u8])->bool {
 let reference=reference::boxed_ref::<u64,AfterError>(Ok(unsafe{WORD}));
 let same=match (result,reference){(Ok(x),Ok(y))=>after_word(x)==*y,_=>false};
 same!='''+('true' if os.environ.get('NEC_INVERT') else 'false')+'\n}'+v[end:]
  if os.environ.get('NEC_RAW_CARRIER'):
   for typ in ['After','Live']:
    v=v.replace('let x:'+typ+'=kani::any();','let x:'+typ+'=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<'+typ+'>()]>())};')
  out[n]=v
 if os.environ.get('NEC_RAW_CARRIER'):
  n='crates/aspis-statement/src/pool_v1/NEC_decode.rs';v=out[n]
  for typ in ['After','Live']:
   v=v.replace('let x:'+typ+'=kani::any();','let x:'+typ+'=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<'+typ+'>()]>())};')
  out[n]=v
 if os.environ.get('NEC_PURE_POST'):
  name='crates/aspis-statement/src/pool_v1/NEC_reference.rs'
  out[name]+='\npub fn reply_ref<T,E>(reply:Result<T,E>)->Result<T,ChildError<E>> {\n match reply { Ok(value)=>Ok(value),Err(error)=>Err(ChildError::Child(error)) }\n}\n'
  name='crates/aspis-statement/src/pool_v1/NEC_decode.rs';v=out[name]
  v=v.replace('reference::boxed_ref','reference::reply_ref')
  if os.environ.get('NEC_PURE_VALUE'):v=v.replace('after_word(x)==*y','after_word(x)==y')
  else:v=v.replace('after_word(x)==**y','after_word(x)==*y')
  v=v.replace('live_word(x)==**y','live_word(x)==*y')
  out[name]=v
 if os.environ.get('NEC_ENVELOPE'):
  name='crates/aspis-statement/src/pool_v1/NEC_decode.rs';v=out[name]
  old='let bytes:[u8;688]=kani::any();let _=super::decode_pair_afterstate_boxed_v1(&bytes);'
  new='let bytes:[u8;688]=kani::any();let length:usize=kani::any();kani::assume(length<=688);let _=super::decode_pair_afterstate_boxed_v1(&bytes[..length]);'
  assert old in v
  out[name]=v.replace(old,new)
 n='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
 s=frozen(n)
 for name,post,length in [('decode_pair_afterstate_boxed_v1','post_after',688),('decode_pair_live_snapshot_boxed_v1','post_live',800)]:
  attrs='#[cfg_attr(kani,kani::requires(bytes.len()=='+str(length)+'))]\n#[cfg_attr(kani,kani::ensures(|r| NEC_decode::'+post+'(r,bytes)))]\n'
  attrs+='#[cfg_attr(kani,kani::modifies(&raw mut NEC_decode::CALLS,&raw mut NEC_decode::PTR,&raw mut NEC_decode::LEN,&raw mut NEC_decode::WORD,&raw mut NEC_decode::AFTER_ERROR,&raw mut NEC_decode::LIVE_ERROR))]\n'
  if os.environ.get('NEC_PURE_VALUE') and name=='decode_pair_afterstate_boxed_v1':
   attrs=attrs[:attrs.index('#[cfg_attr(kani,kani::modifies')]+ '#[cfg_attr(kani,kani::modifies())]\n'
  if os.environ.get('NEC_ENVELOPE') and name=='decode_pair_afterstate_boxed_v1':attrs=attrs.replace('bytes.len()==688','bytes.len()<=688')
  s=s.replace('fn '+name+'(',attrs+'fn '+name+'(',1)
 out[n]=s+'\n#[cfg(kani)] #[path="NEC_decode.rs"] mod NEC_decode;\n'
 if os.environ.get('NEC_LIVE_STEP'):
  n='crates/aspis-statement/src/lib.rs';out[n]+='\n#[cfg(kani)] mod NEC_live_step;\n'
  out['crates/aspis-statement/src/NEC_live_step.rs']=template('NEC_live_step').replace('NEC_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false')
 if os.environ.get('NEC_FIDELITY'):
  n='crates/aspis-statement/src/lib.rs';out[n]+='\n#[cfg(kani)] mod NEC_fidelity;\n'
  v=template('NEC_fidelity').replace('NEC_FIDELITY_INVERT','true' if os.environ.get('NEC_FIDELITY_INVERT') else 'false')
  v=v.replace('NEC_FIDELITY_MODIFIES','' if os.environ.get('NEC_FIDELITY_BAD_MODIFIES') else '&raw mut COUNT')
  v=v.replace('NEC_FIDELITY_STUB','#[kani::stub_verified(shape)]' if os.environ.get('NEC_FIDELITY_STUB') else '')
  out['crates/aspis-statement/src/NEC_fidelity.rs']=v
 if os.environ.get('NEC_LIVE_HEADER'):
  path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';v=out[path]
  attribute='#[cfg_attr(kani,kani::requires(bytes.len()<=800))]\n#[cfg_attr(kani,kani::ensures(|r| NEC_live_header::post(r,bytes)))]\n#[cfg_attr(kani,kani::modifies())]\n'
  v=v.replace('pub fn decode_pool_v1_pair_live_snapshot_v1(',attribute+'pub fn decode_pool_v1_pair_live_snapshot_v1(',1)
  out[path]=v+'\n#[cfg(kani)] #[path="NEC_live_header.rs"]mod NEC_live_header;\n'
  out['crates/aspis-statement/src/pool_v1/NEC_live_header.rs']=template('NEC_live_header').replace('NEC_HEADER_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false')
  out['crates/aspis-statement/src/pool_v1/NEC_live_header_reference.rs']=template('NEC_live_header_reference')
 if os.environ.get('NEC_LIVE_STEP') or os.environ.get('NEC_LIVE_HEADER'):
  path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';text=frozen(path)
  body=text.split('pub fn decode_pool_v1_pair_live_snapshot_v1(',1)[1].split('pub fn encode_pool_v1_pair_late_public_statement_v1(',1)[0]
  cells=[tuple(map(int,m)) for m in re.findall(r'decode_digest_canonical\(\s*crate::atomic_statement::unwrap_fixed_slice\(\s*bytes\[(\d+)\.\.(\d+)\]',body)]
  assert cells==[(128+32*i,160+32*i) for i in range(21)],cells
  (E/'NEC_LIVE_CALL_SITES.json').write_text(json.dumps(dict(revision=R,source=path,function='decode_pool_v1_pair_live_snapshot_v1',body_sha256=hashlib.sha256(body.encode()).hexdigest(),cells=cells,domain='slot<21, byte<32; full arbitrary byte contents at the native call prefix',lean_geometry='NEC_LiveGeometry'),indent=1)+'\n')
 if os.environ.get('NEC_CTOR'):
  path='programs/r1-cost-probe/src/lib.rs';out[path]='#![cfg_attr(kani, feature(allocator_api))]\n'+frozen(path)+'\n#[cfg(kani)]mod NEC_kmx {extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));}\n'
  path='programs/r1-cost-probe/src/r1_pool_adapter.rs';v=frozen(path)
  for name,expect,kind in [('transfer_statement_box','expected_transfer',0),('withdrawal_statement_box','expected_withdrawal',1)]:
   attr='#[cfg_attr(kani,kani::ensures(|r| NEC_ctor::post(r,old(NEC_ctor::'+expect+'(&common,&public)),'+str(kind)+')))]\n'
   attr+='#[cfg_attr(kani,kani::modifies((&*common as *const PoolV1PairForestTerminalCommonV1).cast_mut(),&raw mut NEC_ctor::CALLS,&raw mut NEC_ctor::SEEN,&raw mut NEC_ctor::SEEN_KIND))]\n'
   v=v.replace('fn '+name+'(',attr+'fn '+name+'(',1)
  out[path]=v+'\n#[cfg(kani)]#[path="NEC_ctor.rs"]mod NEC_ctor;\n'
  v=template('NEC_ctor').replace('NEC_CTOR_MODE',os.environ.get('NEC_CTOR_MODE','0')).replace('cfg!(NEC_ctor_negative)','true' if os.environ.get('NEC_INVERT') else 'false')
  v=v.replace('let g:u8=kani::any();','let g:u8='+os.environ.get('NEC_CTOR_GROUP','0')+';')
  if os.environ.get('NEC_CTOR_FIELD'):v=v.replace('let f:u8=kani::any();','let f:u8='+os.environ['NEC_CTOR_FIELD']+';')
  if os.environ.get('NEC_CTOR_PURE'):
   v=v.replace('let call=unsafe{CALLS==1 && SEEN_KIND==kind && SEEN==word};','let call=true;')
   v=v.replace('let (kind,word)=observe(s);unsafe{CALLS=CALLS.wrapping_add(1);SEEN=word;SEEN_KIND=kind;}','let _=s;')
  if os.environ.get('NEC_CTOR_CALL_ONLY'):
   v=v.replace('(value && call) !=','call !=')
  out['programs/r1-cost-probe/src/NEC_ctor.rs']=v
  out['programs/r1-cost-probe/src/NEC_ctor_reference.rs']=template('NEC_ctor_reference')
 if os.environ.get('NEC_BINDING'):
  path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';v=frozen(path)
  attr='#[cfg_attr(kani,kani::ensures(|r| NEC_binding::post(r,statement,result)))]\n#[cfg_attr(kani,kani::modifies())]\n'
  v=v.replace('pub fn validate_pool_v1_pair_forest_terminal_result_against_statement_v1(',attr+'pub fn validate_pool_v1_pair_forest_terminal_result_against_statement_v1(',1)
  out[path]=v+'\n#[cfg(kani)]#[path="NEC_binding.rs"]mod NEC_binding;\n'
  v=template('NEC_binding').replace('NEC_BINDING_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false')
  if os.environ.get('NEC_BINDING_DERIVED'):
   begin=v.index(' let v=PoolV1PairForestTerminalResultV1{');end=v.index('\n unsafe{FIRST=',begin)
   v=v[:begin]+' let v=derived(&s);'+v[end:]
   v+='\npub fn derived(s:&PoolV1PairForestTerminalStatementV1)->PoolV1PairForestTerminalResultV1 {PoolV1PairForestTerminalResultV1{transition_kind:s.transition_kind(),master_account:s.common().master_account,selected_lane_account:s.common().selected_lane_account,output_lane:s.common().output_lane,nullifier:*s.nullifier(),verified_afterstate:s.common().lane_transition.candidate_afterstate}}\n'
   v=v.replace('mismatch(s,v),PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch','false,PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch')
   out[path]=out[path].replace('#[cfg_attr(kani,kani::ensures(|r| NEC_binding::post', '#[cfg_attr(kani,kani::requires(*result==NEC_binding::derived(statement)))]\n#[cfg_attr(kani,kani::ensures(|r| NEC_binding::post')
  out['crates/aspis-statement/src/pool_v1/NEC_binding.rs']=v
  out['crates/aspis-statement/src/pool_v1/NEC_binding_reference.rs']=template('NEC_binding_reference')
 if os.environ.get('NEC_STATIC'):
  path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';v=frozen(path)
  for name,post,length in [('decode_pair_afterstate_boxed_v1','after_post',688),('decode_pair_live_snapshot_boxed_v1','live_post',800)]:
   attr='#[cfg_attr(kani,kani::requires(bytes.len()=='+str(length)+'))]\n#[cfg_attr(kani,kani::ensures(|r| NEC_static_decode::'+post+'(r)))]\n#[cfg_attr(kani,kani::modifies())]\n'
   v=v.replace('fn '+name+'(',attr+'fn '+name+'(',1)
  out[path]=v+'\n#[cfg(kani)]#[path="NEC_static_decode.rs"]mod NEC_static_decode;\n'
  out['crates/aspis-statement/src/pool_v1/NEC_static_decode.rs']=template('NEC_static_decode').replace('NEC_STATIC_GROUP',os.environ.get('NEC_GROUP','0')).replace('NEC_STATIC_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false')
  if os.environ.get('NEC_STATIC_AFTER_BOUND'):out['crates/aspis-statement/src/pool_v1/NEC_static_decode.rs']=out['crates/aspis-statement/src/pool_v1/NEC_static_decode.rs'].replace('i<if GROUP==2||GROUP==3{32}else{8}','i<8')
  out['crates/aspis-statement/src/pool_v1/NEC_static_reference.rs']=template('NEC_pure_reference')
 if os.environ.get('NEC_LIVE_VALUE'):
  path='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';v=frozen(path)
  attr='#[cfg_attr(kani,kani::requires(bytes.len()==800 && bytes[..48]==NEC_live_decode::make_bytes()[..48]))]\n#[cfg_attr(kani,kani::ensures(|r| NEC_live_decode::post(r)))]\n#[cfg_attr(kani,kani::modifies(&raw mut NEC_live_decode::NEXT))]\n'
  # make_bytes is nondeterministic in its unused tail, so use the pure header
  # reference instead of invoking it in a contract.
  attr=attr.replace('bytes[..48]==NEC_live_decode::make_bytes()[..48]','NEC_live_decode::header::live_header_ref(bytes.len(),bytes[..48].try_into().unwrap())==0')
  out[path]=v.replace('pub fn decode_pool_v1_pair_live_snapshot_v1(',attr+'pub fn decode_pool_v1_pair_live_snapshot_v1(',1)+'\n#[cfg(kani)]#[path="NEC_live_decode.rs"]mod NEC_live_decode;\n'
  v=template('NEC_live_decode').replace('NEC_LIVE_VALUE_GROUP',os.environ.get('NEC_GROUP','0')).replace('NEC_LIVE_VALUE_NEGATIVE','true' if os.environ.get('NEC_INVERT') else 'false').replace('NEC_LIVE_REJECT','true' if os.environ.get('NEC_LIVE_REJECT') else 'false').replace('NEC_LIVE_DIGEST_REJECT','true' if os.environ.get('NEC_LIVE_DIGEST_REJECT') else 'false')
  values=list(b'ASPLIVE1')+[1]+[0]*7+[65,83,80,80,65,73,82,49,1,20,21,7,1,1,1,1]+[0]*16
  v=v.replace('NEC_LIVE_HEADER_ASSIGNMENTS',''.join('b['+str(i)+']='+str(x)+';' for i,x in enumerate(values)))
  v+='\n#[path="NEC_live_header_reference.rs"]pub mod header;\n'
  v=v.replace('static mut NEXT:','pub static mut NEXT:')
  out['crates/aspis-statement/src/pool_v1/NEC_live_decode.rs']=v
  out['crates/aspis-statement/src/pool_v1/NEC_live_value_reference.rs']=template('NEC_pure_reference')
  out['crates/aspis-statement/src/pool_v1/NEC_live_header_reference.rs']=template('NEC_live_header_reference')
 patch=[]
 for n,s in out.items():
  r=subprocess.run(['git','show',R+':'+n],capture_output=True,text=True);b=r.stdout if r.returncode==0 else ''
  patch.append(''.join(difflib.unified_diff(b.splitlines(True),s.splitlines(True),fromfile='a/'+n if b else '/dev/null',tofile='b/'+n)))
 (E/'NEC_native.patch').write_text(''.join(patch));return out
