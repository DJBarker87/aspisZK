from pathlib import Path
import subprocess,sys,json,hashlib,re
from NFD_native_patch import E,frozen,program,helpers
shape,mode=sys.argv[1:3];slot=int(sys.argv[3]);assert 0<=slot<15;assert shape in ['common','common_actual','prefix','prefix_match','finish'];assert mode in ['positive','negative','wrong_common','wrong_reply','wrong_allocation']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';source=frozen(p);a=source.index('fn reconstruct_asq8_statement(');z=source.index('\n}',a)+2;original=source[a:z]
base=helpers();auth=''
# Typed arbitrary fields only. No byte transmute and no writable static.
structs=[('PoolIdentityV1','format.rs'),('VerifierPolicyV1','format.rs'),('PoolV1PairForestMasterV1','pair_forest_accounts.rs'),('IncrementalMerkleTreeV1','incremental_merkle.rs'),('PoolV1PairForestCheckpointV1','pair_forest_accounts.rs'),('PoolV1PairForestLaneStateV1','pair_forest_accounts.rs')]
nested={n:'any_'+n+'()' for n,_ in structs}
for name,file in structs:
 f=frozen('crates/aspis-statement/src/pool_v1/'+file);block=f.split('pub struct '+name+' {',1)[1].split('\n}',1)[0];fields=re.findall(r'pub (\w+):\s*([^\n]+),',block)
 vals=[]
 for key,ty in fields:
  v=nested.get(ty,'['+','.join(['kani::any()']*8)+']' if ty=='[u64; POOL_V1_PAIR_FOREST_LANE_COUNT]' else 'NEE_digest()' if ty=='Digest' else 'NEE_frontier()' if ty.startswith('[Digest;') else 'M31(kani::any())' if ty=='M31' else 'kani::any()')
  vals.append(key+':'+v)
 auth+='fn any_'+name+'()->'+name+'{'+name+'{'+','.join(vals)+'}}\n'
# Fully initialize valid typed boxes, then assign every scalar independently.
# This avoids passing large symbolic aggregates through Box::new/copy stubs.
definitions={}
for typename,file in structs+[('PoolV1PairLiveSnapshotV1','pair_tree_profile.rs')]:
 text=frozen('crates/aspis-statement/src/pool_v1/'+file);block=text.split('pub struct '+typename+' {',1)[1].split('\n}',1)[0]
 definitions[typename]=re.findall(r'pub (\w+):\s*([^\n]+),',block)
definitions['AuthenticatedAsq8Accounts']=[('master_account','[u8; 32]'),('checkpoint_account','[u8; 32]'),('selected_lane_account','[u8; 32]'),('master','Box<PoolV1PairForestMasterV1>'),('checkpoint','Box<PoolV1PairForestCheckpointV1>'),('selected_lane','Box<PoolV1PairForestLaneStateV1>'),('live_snapshot','Box<PoolV1PairLiveSnapshotV1>')]
def array(ty):
 m=re.fullmatch(r'\[(.+);\s*([^]]+)\]',ty)
 if not m:return None
 count={'POOL_V1_TREE_DEPTH':20,'POOL_V1_PAIR_TREE_DEPTH':20,'POOL_V1_PAIR_FOREST_LANE_COUNT':8}.get(m[2],int(m[2]) if m[2].isdigit() else None)
 assert count is not None,ty
 return m[1].strip(),count
def initial(ty):
 if ty.startswith('Box<'):return 'Box::new('+initial(ty[4:-1])+')'
 if ty in definitions:return ty+'{'+','.join(n+':'+initial(t) for n,t in definitions[ty])+'}'
 if ty=='Digest':return '[M31(0);8]'
 if ty=='M31':return 'M31(0)'
 if ty=='bool':return 'false'
 if array(ty):
  element,count=array(ty);return '['+initial(element)+';'+str(count)+']'
 assert ty in ['u8','u32','u64','usize'],ty
 return '0'
writes=[]
def initialize(path,ty):
 if ty.startswith('Box<'):return initialize(path,ty[4:-1])
 if ty in definitions:
  for n,t in definitions[ty]:initialize(path+'.'+n,t)
 elif ty=='Digest':
  for i in range(8):initialize(path+'['+str(i)+']','M31')
 elif array(ty):
  element,count=array(ty)
  for i in range(count):initialize(path+'['+str(i)+']',element)
 else:
  assert ty in ['u8','u32','u64','usize','bool','M31'],ty
  writes.append((path,'M31(kani::any())' if ty=='M31' else 'kani::any()'))
initialize('a','AuthenticatedAsq8Accounts');assert len({n for n,_ in writes})==len(writes)
def arbitrary(ty):
 if ty.startswith('Box<'):return 'Box::new('+arbitrary(ty[4:-1])+')'
 if ty in definitions:return ty+'{'+','.join(n+':'+arbitrary(t) for n,t in definitions[ty])+'}'
 if ty=='Digest':return 'NEE_digest()'
 if ty=='M31':return 'M31(kani::any())'
 if array(ty):
  element,count=array(ty)
  return '['+','.join(arbitrary(element) for _ in range(count))+']'
 assert ty in ['u8','u32','u64','usize','bool'],ty
 return 'kani::any()'
auth+='fn auth()->Box<AuthenticatedAsq8Accounts>{Box::new('+arbitrary('AuthenticatedAsq8Accounts')+')}\n'
(E/'NFD_AUTH_INITIALIZATION.json').write_text(json.dumps(dict(method='direct safe typed arbitrary constructors: no zero baseline, no subsequent overwrites; EVERY scalar independently arbitrary',unread_cells_not_fixed=True,scalar_leaves=len(writes),writes=writes,unsafe=False),indent=1)+'\n')
auth+='fn request()->PoolV1PairForestTerminalRequestV1{let s=NEE_statement();let public=match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>PoolV1PairForestTerminalPaymentV1::Withdrawal(public)};PoolV1PairForestTerminalRequestV1{verifier_profile:kani::any(),verifier_release:kani::any(),pool_program:kani::any(),public}}\n'
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFD_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFD_KMX::KMX_copy_from_slice)]
'''
fields=[];all_fields=[]
if shape in ['common','common_actual']:
 fields=[('master_account[j]','a.master_account[j]'),('checkpoint_account[j]','a.checkpoint_account[j]'),('selected_lane_account[j]','a.selected_lane_account[j]'),('output_lane','a.selected_lane.lane_id'),('checkpoint_sequence','a.checkpoint.checkpoint_sequence'),('historical_global_anchor[i].0','a.checkpoint.global_root[i].0'),('lane_transition.live_snapshot.pool[j]','a.live_snapshot.pool[j]'),('lane_transition.live_snapshot.deployment_domain[j]','a.live_snapshot.deployment_domain[j]'),('lane_transition.live_snapshot.sequence','a.live_snapshot.sequence'),('lane_transition.live_snapshot.next_pair_index','a.live_snapshot.next_pair_index'),('lane_transition.live_snapshot.current_root[i].0','a.live_snapshot.current_root[i].0'),('lane_transition.live_snapshot.frontier[k][i].0','a.live_snapshot.frontier[k][i].0'),('lane_transition.candidate_afterstate.next_pair_index','c.next_pair_index'),('lane_transition.candidate_afterstate.next_root[i].0','c.next_root[i].0'),('lane_transition.candidate_afterstate.next_frontier[k][i].0','c.next_frontier[k][i].0')]
 all_fields=fields;fields=[fields[slot]]
 left='match selector{'+','.join(str(n)+'=>out.'+l+' as u64' for n,(l,r) in enumerate(fields))+',_=>0}'
 right='match selector{'+','.join(str(n)+'=>'+r+' as u64'+('^1' if n==0 and mode=='negative' else '') for n,(l,r) in enumerate(fields))+',_=>0}'
 checks='assert!(('+left+')==('+right+'));'
 native='one native elemental initializer read/write on actual typed Auth/Candidate/Common carriers; Box allocation join remains OPEN'
 body=base+auth+attrs+'fn reconstruction_slice(){let a=auth();let c=NEE_common().lane_transition.candidate_afterstate;let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let selector:usize=kani::any();kani::assume(i<8&&j<32&&k<20&&selector<1);let mut out=NEE_common();out.'+fields[0][0]+'='+fields[0][1]+';'+checks+'}\n'
 if shape=='common_actual':
  af=frozen('programs/r1-cost-probe/src/r1_pool_adapter.rs');aa=af.index('fn asq8_common(');az=af.index('\n}',aa)+2;actual=af[aa:az]
  native=actual.replace('fn asq8_common(','fn native(').replace(') -> Box<PoolV1PairForestTerminalCommonV1>','f:&mut Frame) -> Box<PoolV1PairForestTerminalCommonV1>').replace('    Box::new(','    let out=Box::new(').replace('    })\n}','    });\n    f.allocated=&*out;\n    out\n}')
  if mode=='wrong_allocation':native=native.replace('    out\n}', '    Box::new(*out)\n}')
  frame='struct Frame{allocated:*const PoolV1PairForestTerminalCommonV1}\n'
  body=base+auth+frame+native+attrs+'fn reconstruction_slice(){let a=auth();let c=NEE_common().lane_transition.candidate_afterstate;let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let selector:usize=kani::any();kani::assume(i<8&&j<32&&k<20&&selector<1);let mut frame=Frame{allocated:core::ptr::null()};let out=native(&a,&c,&mut frame);assert!(core::ptr::eq(out.as_ref(),frame.allocated));'+checks+'}\n'
  original=actual

elif shape in ['prefix','prefix_match']:
 native=original[:original.index('    let common =')].replace('fn reconstruct_asq8_statement(','fn prefix(').replace('Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError>','ProgramResult')+'    Ok(())\n}\n'
 body=base+auth+native+attrs+'''fn reconstruction_slice(){let r=request();let a=auth();let c=NEE_common().lane_transition.candidate_afterstate;let requested=match r.public{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p.asset_id.0,PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>p.asset_id.0};let live=a.live_snapshot.next_pair_index;let good=live!=u64::MAX&&live.wrapping_add(1)==c.next_pair_index;let expected=if !good{Err(ProgramError::InvalidAccountData)}else if a.master.identity.asset_id.0!=requested@BAD@{Err(ProgramError::InvalidInstructionData)}else{Ok(())};assert!(prefix(&r,&a,&c)==expected);}
'''.replace('@BAD@','^1' if mode=='negative' else '')
 if shape=='prefix_match':
  begin=body.index('let expected=if !good')
  body=body[:begin]+'let expected:u8=if !good{1}else if a.master.identity.asset_id.0!=requested'+('^1' if mode=='negative' else '')+'{2}else{0};let observed:u8=match prefix(&r,&a,&c){Ok(())=>0,Err(ProgramError::InvalidAccountData)=>1,Err(ProgramError::InvalidInstructionData)=>2,Err(_)=>3};assert!(observed==expected); }\n'
else:
 native=original[original.index('    let common ='):].replace('asq8_common(authenticated, candidate_afterstate)','common(authenticated, candidate_afterstate,f)').replace('transfer_statement_box(common, public)','transfer(common, public,f)').replace('withdrawal_statement_box(common, public)','withdrawal(common, public,f)')
 native='fn finish(request:&PoolV1PairForestTerminalRequestV1,authenticated:&AuthenticatedAsq8Accounts,candidate_afterstate:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{\n'+native
 # A child result is Ok(arbitrary typed Box) or Err(InvalidInstructionData),
 # precisely the constructor range proved by NFD_BoxModel and its native pair.
 frame='''struct Frame<'a>{root:&'a PoolV1PairForestTerminalRequestV1,a:&'a AuthenticatedAsq8Accounts,c:&'a PoolV1PairVerifiedAfterstateV1,common:Option<Box<PoolV1PairForestTerminalCommonV1>>,reply:Option<Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>>,common_ptr:*const PoolV1PairForestTerminalCommonV1,calls:u8,branch:u8,i:usize,j:usize,selector:usize}
fn common(a:&AuthenticatedAsq8Accounts,c:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Box<PoolV1PairForestTerminalCommonV1>{assert!(f.calls==0&&core::ptr::eq(a,f.a)&&core::ptr::eq(c,f.c));f.calls=1;let out=f.common.take().unwrap();f.common_ptr=out.as_ref();out}
'''
 funcs=''
 for name,variant,ty in [('transfer','PrivateTransfer','PoolV1PrivateTransferPublicV1'),('withdrawal','Withdrawal','PoolV1WithdrawalPublicV1')]:
  fields=['pool[j]','deployment_domain[j]','anchor_sequence','anchor_root[i].0','nullifier[i].0','asset_id.0','change_commitment[i].0']+(['recipient_commitment[i].0'] if name=='transfer' else ['amount','destination_token_account[j]'])
  left='match f.selector{'+','.join(str(i)+'=>p.'+x+' as u64' for i,x in enumerate(fields))+',_=>0}'
  right='match f.selector{'+','.join(str(i)+'=>expected.'+x+' as u64'+('^1' if mode=='negative' and i==slot else '') for i,x in enumerate(fields))+',_=>0}'
  checks='assert!(('+left+')==('+right+'));'
  funcs+='fn '+name+'(common:Box<PoolV1PairForestTerminalCommonV1>,p:'+ty+',f:&mut Frame)->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{assert!(f.calls==1&&core::ptr::eq(common.as_ref(),f.common_ptr));f.calls=2;f.branch='+('1' if name=='transfer' else '2')+';let i=f.i;let j=f.j;match &f.root.public{PoolV1PairForestTerminalPaymentV1::'+variant+'(expected)=>{'+checks+'},_=>assert!(false)};'+('Err(ProgramError::InvalidAccountData)' if mode=='wrong_reply' else 'f.reply.take().unwrap()')+'}\n'
 if mode=='wrong_common':native=native.replace('transfer(common, public,f)','transfer(Box::new(*common), public,f)').replace('withdrawal(common, public,f)','withdrawal(Box::new(*common), public,f)')
 body=base+auth+frame+funcs+native+attrs+'''fn reconstruction_slice(){let r=request();let a=auth();let c=NEE_common().lane_transition.candidate_afterstate;let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<8&&j<32);let selector:usize=kani::any();kani::assume(selector<9);let good:bool=kani::any();let reply=if good{Ok(Box::new(NEE_statement()))}else{Err(ProgramError::InvalidInstructionData)};let expected_ptr=match &reply{Ok(b)=>b.as_ref() as *const _,Err(_)=>core::ptr::null()};let branch=match r.public{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)=>1,PoolV1PairForestTerminalPaymentV1::Withdrawal(_)=>2};let mut f=Frame{root:&r,a:&a,c:&c,common:Some(Box::new(NEE_common())),reply:Some(reply),common_ptr:core::ptr::null(),calls:0,branch:0,i,j,selector};let actual=finish(&r,&a,&c,&mut f);assert!(f.calls==2&&f.branch==branch);match actual{Ok(out)=>assert!(good&&core::ptr::eq(out.as_ref(),expected_ptr)),Err(ProgramError::InvalidInstructionData)=>assert!(!good),Err(_)=>assert!(false)};}
'''
if shape=='finish':
 body=body.replace('kani::assume(selector<9);','kani::assume(selector=='+str(slot)+');')
 if mode=='negative' and slot==8:body=body.replace('let a=auth();','kani::assume(matches!(r.public,PoolV1PairForestTerminalPaymentV1::Withdrawal(_)));let a=auth();')
program(body,'NFD_reconstruct')
(E/'NFD_RECONSTRUCT_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,field_slot=slot,fields=fields,all_fields=all_fields,frozen_body=original,native=native,domain='every typed Request/Auth/Candidate; all word values; valid owned Box carriers; arbitrary observed byte/word indices',classification='source-isolated elemental common initializer or prefix/finish; native common allocation/move stays OPEN; local records only; finish constructor reply range needs NFD_BoxModel plus complete native child certificates; no inherited NEC static credit'),indent=1)+'\n')
