"""Exact guard/continuation split; no assumption of root or child success."""
import subprocess
import NFD_validate as v
from NFD_native_checks import native
from NFD_composition_support import source,structural
from NFD_bridge_checks import REV
E=v.E
F='programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement'
P=F.split('::')[0]
THMS=['NEU_ReconstructCore.result_state_effects','NEU_ReconstructAdopted.result_state_effects','NEU_CallDomains.reached_domains','NEU_CallDomains.common_packet','NEU_CallDomains.transfer_packet','NEU_CallDomains.withdrawal_packet','NEU_CallDomains.transfer_reply_range','NEU_CallDomains.withdrawal_reply_range']
ATTEMPTS=['NFD_K085','NFD_K086']+[f'NFD_K{n:03}' for n in range(91,111)]
EXTRAS=['NFD_FINISH_TEMPLATE.json','NFD_AUTH_INITIALIZATION.json']
CLASS='source-ordered checked-add/asset prefix, same immutable Auth/Candidate; same owned common Box into selected raw payment constructor; complete child reply and ordered validator effects'
def finish_source(slot,mode):
 t=v.read(E/'NFD_FINISH_TEMPLATE.json');assert v.sha(t['source'].encode())==t['source_sha256']=='5a4d3ceda1601288d42f1b27a5c024d8c479b23d091a3769c153468e926869d9'
 s=t['source'].replace('kani::assume(selector==0);','kani::assume(selector=='+str(slot)+');')
 if mode=='negative':
  # Both variant projections have identical first seven field selectors.
  import re
  s=re.sub(r'('+str(slot)+r'=>expected\.[^,}]+ as u64)([,}])',r'\1^1\2',s)
  if slot==8:s=s.replace('let a=auth();','kani::assume(matches!(r.public,PoolV1PairForestTerminalPaymentV1::Withdrawal(_)));let a=auth();')
 if mode=='wrong_common':s=s.replace('transfer(common, public,f)','transfer(Box::new(*common), public,f)').replace('withdrawal(common, public,f)','withdrawal(Box::new(*common), public,f)')
 if mode=='wrong_reply':s=s.replace('f.reply.take().unwrap()','Err(ProgramError::InvalidAccountData)')
 return s
def check(c,base):
 assert c['subject']==F
 n=c['native_certificate'];assert n==dict(function=F,complete=True,domain='all typed Request/Auth/Candidate; raw noncanonical fields admitted; no accepted-run condition',prefix=['NFD_K085','NFD_K086'],pairs=[[f'NFD_K{91+2*i:03}',f'NFD_K{92+2*i:03}'] for i in range(9)],controls=['NFD_K109','NFD_K110'])
 original=subprocess.check_output(['git','show',REV+':'+P],text=True);a=original.index('fn reconstruct_asq8_statement(');original=original[a:original.index('\n}',a)+2]
 for a,positive in [('NFD_K085',True),('NFD_K086',False)]:
  snap=native(a,positive);m=v.read(E/(a+'-shape.json'));s=source(snap['NFD_native_contracts.patch'],'NFD_reconstruct')
  assert m['shape']=='prefix_match' and m['mode']==('positive' if positive else 'negative') and m['frozen_body']==original
  expected=original[:original.index('    let common =')].replace('fn reconstruct_asq8_statement(','fn prefix(').replace('Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError>','ProgramResult')+'    Ok(())\n}\n'
  assert m['native']==expected and expected in s
  assert 'let expected:u8=if !good{1}else if a.master.identity.asset_id.0!=requested'+('' if positive else '^1')+'{2}else{0};' in s
  assert 'match prefix(&r,&a,&c){Ok(())=>0,Err(ProgramError::InvalidAccountData)=>1,Err(ProgramError::InvalidInstructionData)=>2,Err(_)=>3};assert!(observed==expected);' in s
  assert 'let good=live!=u64::MAX&&live.wrapping_add(1)==c.next_pair_index;' in s
  assert 'kani::assume' not in s.split('fn reconstruction_slice(){')[1]
 for slot in range(9):
  for off,mode in enumerate(['positive','negative']):
   a=f'NFD_K{91+2*slot+off:03}';snap=native(a,mode=='positive');m=v.read(E/(a+'-shape.json'))
   assert m['shape']=='finish' and m['mode']==mode and m['field_slot']==slot and m['frozen_body']==original
   assert source(snap['NFD_native_contracts.patch'],'NFD_reconstruct')==finish_source(slot,mode)
 for a,mode in [('NFD_K109','wrong_common'),('NFD_K110','wrong_reply')]:
  snap=native(a,False);assert source(snap['NFD_native_contracts.patch'],'NFD_reconstruct')==finish_source(0,mode)
 s=finish_source(0,'positive');m=v.read(E/'NFD_K091-shape.json')
 expected=original[original.index('    let common ='):].replace('asq8_common(authenticated, candidate_afterstate)','common(authenticated, candidate_afterstate,f)').replace('transfer_statement_box(common, public)','transfer(common, public,f)').replace('withdrawal_statement_box(common, public)','withdrawal(common, public,f)')
 assert m['native'].split('{\n',1)[1]==expected and m['native'] in s
 assert all(x in s for x in ['core::ptr::eq(a,f.a)','core::ptr::eq(c,f.c)','core::ptr::eq(common.as_ref(),f.common_ptr)','core::ptr::eq(out.as_ref(),expected_ptr)','Err(_)=>assert!(false)','f.calls==2&&f.branch==branch'])
 # Safe arbitrary actual-type factory is identical to the already checked
 # common certificate; all words, including unread fields, remain arbitrary.
 common=v.read(E/'NFD_COMMON_TEMPLATE.json')['source'];assert s[s.index('fn auth()'):s.index('struct Frame')] == common[common.index('fn auth()'):common.index('struct Frame')]
 return structural(c,F,THMS,base,ATTEMPTS,EXTRAS,CLASS)
