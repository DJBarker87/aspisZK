"""Additional admission for newly completed S bridges; baseline gates stay intact.

Native support, full emitted Result/trace substitution and every call domain
are separate requirements. A model theorem or a subset of windows is OPEN.
"""
from pathlib import Path
import hashlib,json,lzma,re,copy,difflib
from functools import lru_cache
P='programs/r1-cost-probe/src/r1_pool_adapter.rs::'
from NEU_decoder_checks import FUNCTIONS as DECODER_FUNCTIONS
FUNCTIONS=[P+n for n in ['asq8_common','transfer_statement_box','withdrawal_statement_box','reconstruct_asq8_statement']]+DECODER_FUNCTIONS
COMMON=['master_account[j]','checkpoint_account[j]','selected_lane_account[j]','output_lane','checkpoint_sequence','historical_global_anchor[i].0','lane_transition.live_snapshot.pool[j]','lane_transition.live_snapshot.deployment_domain[j]','lane_transition.live_snapshot.sequence','lane_transition.live_snapshot.next_pair_index','lane_transition.live_snapshot.current_root[i].0','lane_transition.live_snapshot.frontier[k][i].0','lane_transition.candidate_afterstate.next_pair_index','lane_transition.candidate_afterstate.next_root[i].0','lane_transition.candidate_afterstate.next_frontier[k][i].0']
PUBLIC=['pool[j]','deployment_domain[j]','anchor_sequence','anchor_root[i].0','nullifier[i].0','asset_id.0','change_commitment[i].0']
FIELDS={
 'transfer_statement_box':['common.'+x for x in COMMON]+['public.'+x for x in PUBLIC+['recipient_commitment[i].0']],
 'withdrawal_statement_box':['common.'+x for x in COMMON]+['public.'+x for x in PUBLIC+['amount','destination_token_account[j]']]}
THEOREMS={
 'asq8_common':['NEU_ReconstructCore.common_result','NEU_CallDomains.common_packet'],
 'transfer_statement_box':['NEU_BoxModel.validator','NEU_BoxModel.transfer','NEU_BoxModel.transfer_result_state_effects','NEU_CallDomains.transfer_packet','NEU_CallDomains.transfer_reply_range'],
 'withdrawal_statement_box':['NEU_BoxModel.validator','NEU_BoxModel.withdrawal','NEU_BoxModel.withdrawal_result_state_effects','NEU_CallDomains.withdrawal_packet','NEU_CallDomains.withdrawal_reply_range'],
 'reconstruct_asq8_statement':['NEU_ReconstructAdopted.result_state_effects','NEU_ReconstructCore.result_state_effects','NEU_CallDomains.reached_domains','NEU_CallDomains.common_packet','NEU_CallDomains.transfer_packet','NEU_CallDomains.withdrawal_packet','NEU_CallDomains.transfer_reply_range','NEU_CallDomains.withdrawal_reply_range','NEU_PublicProjections.transfer_ext','NEU_PublicProjections.withdrawal_ext']}
HELPERS_SHA256='d6a4f0c6eeecd2f2aacbcfef74213102758efbbe53572150350623a492ef94b4'
sha=lambda b:hashlib.sha256(b).hexdigest()
@lru_cache(maxsize=128)
def _unpack(blob,expected):
 raw=lzma.decompress(blob);assert sha(raw)==expected;return json.loads(raw)
def packed(p):
 return _unpack(Path(str(p)+'.xz').read_bytes(),Path(str(p)+'.sha256').read_text().strip())
def inputs(E,a):
 p=E/(a+'-inputs.json')
 d=packed(p) if Path(str(p)+'.xz').is_file() else packed(E/'NEU_SOURCE_HISTORY.json')
 return d[a]
def native_pair(v,pair):
 import NEQ_validate
 assert len(pair)==2 and NEQ_validate.native_pair(*pair,folder=v.E,prefix='NEU_')
 for a in pair:
  r=v.read(v.E/a/'receipt.json');cfg=v.read(v.E/(a+'.json'))
  assert all(r[k]==w for k,w in cfg.items()),'execution config changed'
  snapshots=inputs(v.E,a)
  assert set(snapshots)==set(r['source_hashes'])
  assert all(sha(b.encode())==r['source_hashes'][n] for n,b in snapshots.items())
  assert snapshots['NEU_native_contracts.patch']==(v.E/(a+'-NEU_native_contracts.patch')).read_text()
  assert snapshots['NEU_oracle.patch']==(v.E/(a+'-NEU_oracle.patch')).read_text()
  features={p['name']:set(p['features']) for p in v.read(v.E/(a+'-metadata-pin.json'))['features_all_crates']}
  assert set(cfg['required_statement_features'])<=features['aspis-statement']
  assert {'pool-adapter','private-leaf-salts'}<=features['aspis-r1-cost-probe-program']
  assert not {'no-entrypoint','cu-profiling'}&features['aspis-r1-cost-probe-program']
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe']
  source=snapshots['NEU_native_contracts.patch']
  name=re.search(r'\+\+\+ b/programs/r1-cost-probe/src/(NEU_\w+)\.rs',source).group(1)
  path='programs/r1-cost-probe/src/r1_pool_adapter.rs';frozen=v.frozen_source(path+'::hook')
  changed=frozen+'\n#[cfg(kani)]\n#[path="'+name+'.rs"]\nmod '+name+';\n'
  exact_hook=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
  assert source.startswith(exact_hook),'frozen parent changed beyond cfg(kani) hook'
  assert all(x in ['core::ptr::copy_nonoverlapping','<[u8]>::copy_from_slice'] for x in re.findall(r'kani::stub\(([^,]+),',source))
  assert not any(x in source for x in ['stub_verified','proof_for_contract','kani::requires','static mut','UnsafeCell','Cell<','Atomic'])
 return True

def addition(b,f,ledger,v,reviewed):
 if f in DECODER_FUNCTIONS:
  from NEU_decoder_checks import addition as decoder_addition
  return decoder_addition(b,f,ledger,v,reviewed)
 try:
  assert f in FUNCTIONS and b['function']==f
  assert b['semantic_review_sha256']==reviewed['native-bridge::'+f]==sha(json.dumps({k:w for k,w in b.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  assert b['frozen_revision']==ledger['frozen_revision']
  assert b['trust_classification']=='P6/D188 option A reclassification' and b['new_trust_rows']==[]
  assert b['inner_hypotheses_remaining']==[] and b['full_Result'] and b['same_inputs'] and b['same_state'] and b['same_ordered_effects']
  assert b['native_frame_complete'] and b['domain']=='all typed inputs; no accepted-run or canonicality precondition'
  assert b['physical_qualification']=='root-owned valid typed carriers, fresh Box allocation/cleanup interpretation and ABI; no inner native bridge assumed'
  name=f.rsplit('::',1)[1]
  assert [t['name'] for t in b['theorems']]==THEOREMS[name]
  assert all(v.inherited.theorem(t) for t in b['theorems'])
  pairs=b['native_pairs'];assert pairs
  required=set()
  for pair in pairs:
   for a in pair:
    required.update(str((v.E/n).relative_to(v.R)) for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEU_native_contracts.patch',a+'-NEU_oracle.patch',a+('-box.json' if name in FIELDS else '-reconstruct.json')])
    archive=a+'-inputs.json' if (v.E/(a+'-inputs.json.xz')).is_file() else 'NEU_SOURCE_HISTORY.json'
    required.update(str((v.E/(archive+x)).relative_to(v.R)) for x in ['.xz','.sha256'])
  assert {r['path'] for r in b['support']}==required
  for ref in b['support']:v.inherited.artifact(ref)
  assert all(native_pair(v,pair) for pair in pairs)
  frozen=v.frozen_source(f);a=frozen.index('fn '+name+'(');z=frozen.index('\n}',a)+2;body=frozen[a:z]
  assert b['frozen_body']==body and b['frozen_body_sha256']==sha(body.encode())
  if name in FIELDS:
   assert len(pairs)==len(FIELDS[name])
   for slot,(pair,field) in enumerate(zip(pairs,FIELDS[name])):
    for a,mode in zip(pair,['positive','negative']):
     m=v.read(v.E/(a+'-box.json'));assert m['slot']==slot and m['field']==field and m['mode']==mode
     assert m['domain']=='every typed common/public pair, arbitrary full validation Result and one observed field index'
     assert m['frozen_body']==body
     erased=m['native'].replace('fn native(','fn '+name+'(').replace('\n f:&mut Frame)','\n)').replace('validate(&statement,f)','validate_pool_v1_pair_forest_terminal_statement_v1(&statement)')
     assert erased==body
     source=(v.E/(a+'-NEU_native_contracts.patch')).read_text()
     fragment=source.split('+++ b/programs/r1-cost-probe/src/NEU_box.rs\n',1)[1].split('--- a/',1)[0]
     added='\n'.join(l[1:] for l in fragment.splitlines() if l.startswith('+'))+'\n'
     assert sha(added.split('\nstruct Frame',1)[0].encode())==HELPERS_SHA256
     start=added.index('fn native(');end=added.index('\n}',start)+2
     assert added[start:end]==m['native'],'metadata/caller source mismatch'
     assert re.findall(r'kani::assume\((.*?)\)',source)==['false','i<8&&j<32&&k<20']
     assert f'assert!({field}==f.{field}'+('^1' if mode=='negative' else '')+');' in source
     for text in ['f.place=s','f.reply','match (actual,reply)','core::ptr::eq(out.as_ref(),f.place)','(Err(ProgramError::InvalidInstructionData),Err(_))']:
      assert text in source,text
  else:
   expected=['common'] if name=='asq8_common' else ['prefix','finish']
   assert len(pairs)==len(expected)
   for pair,shape in zip(pairs,expected):
    for a,mode in zip(pair,['positive','negative']):
     m=v.read(v.E/(a+'-reconstruct.json'));assert m['shape']==shape and m['mode']==mode
     source=(v.E/(a+'-NEU_native_contracts.patch')).read_text()
     assert 'unsafe{' not in source and 'transmute' not in source
     assumptions=re.findall(r'kani::assume\((.*?)\)',source)
     assert assumptions==({'common':['i<8&&j<32&&k<20'],'prefix':[],'finish':['i<8&&j<32','selector<9']}[shape])
     if shape=='common':
      assert 'let out=asq8_common(&a,&c)' in source and 'fn asq8_common(' not in source
      for field in COMMON:assert 'assert!(out.'+field+'==' in source
     elif shape=='prefix':
      expected_body=m['frozen_body'][:m['frozen_body'].index('    let common =')].replace('fn reconstruct_asq8_statement(','fn prefix(').replace('Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError>','ProgramResult')+'    Ok(())\n}\n'
      assert m['native']==expected_body
      assert 'live!=u64::MAX&&live.wrapping_add(1)==c.next_pair_index' in source
     else:
      suffix=m['frozen_body'][m['frozen_body'].index('    let common ='):]
      expected_body='fn finish(request:&PoolV1PairForestTerminalRequestV1,authenticated:&AuthenticatedAsq8Accounts,candidate_afterstate:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{\n'+suffix.replace('asq8_common(authenticated, candidate_afterstate)','common(authenticated, candidate_afterstate,f)').replace('transfer_statement_box(common, public)','transfer(common, public,f)').replace('withdrawal_statement_box(common, public)','withdrawal(common, public,f)')
      assert m['native']==expected_body
      for text in ['core::ptr::eq(a,f.a)','core::ptr::eq(c,f.c)','core::ptr::eq(common.as_ref(),f.common_ptr)','f.reply.take().unwrap()','f.calls==2&&f.branch==branch','core::ptr::eq(out.as_ref(),expected_ptr)']:
       assert text in source,text
      for field in PUBLIC+['recipient_commitment[i].0','amount','destination_token_account[j]']:
       assert 'p.'+field+' as u64' in source
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False

def qualifiers(f):
 return ['NEU_'+f.rsplit('::',1)[1]+'.PacketDomain','NEU_'+f.rsplit('::',1)[1]+'.PhysicalInterpretation']

def compose(base,out,packet,reviewed,v):
 """Separate, checked new-evidence admission followed by ordinary closure.

The historical base is checked unchanged before this function. No OPEN bridge
is erased merely by composition: a complete new native/model packet is required.
 """
 additions=packet.get('native_bridge_additions',{})
 assert set(additions)<=set(FUNCTIONS)
 verified={f:b for f,b in additions.items() if addition(b,f,base,v,reviewed)}
 result=copy.deepcopy(out);byfunction={}
 for r in result['rows']:byfunction.setdefault(r['function'],[]).append(r)
 for f,b in verified.items():
  for r in byfunction[f]:
   assert r['frozen_body_verified'] and r['function'] in FUNCTIONS
   r['bridge_status']='CLOSED-CONDITIONAL';r['selected_claims']=['NEU::'+f]
   r['claim_ids']=list(dict.fromkeys(r['claim_ids']+['NEU::'+f]))
   r['named_hypotheses']=[dict(name=n,statement=(b['domain']+'; exact native/semantic carrier law.' if n.endswith('PacketDomain') else b['physical_qualification']),discharged_by=None) for n in qualifiers(f)]
   r['NEU_native_admission']=dict(claim='NEU::'+f,review_sha256=b['semantic_review_sha256'],inherited_rejection_retained=True,new_native_evidence_required=True)
 # Bind selected child qualifications at the SAME caller edges, including the
 # newly admitted claims; no conservative target is removed.
 for f in verified:
  for r in byfunction[f]:
   for ob in r['caller_domain_obligations']:
    g=ob.get('callee')
    if g in verified:
     ob['callee_claims']=['NEU::'+g];ob['callee_local_status']='CLOSED-CONDITIONAL'
     ob['required_named_hypotheses']=qualifiers(g)
 def accepted(c,subject,f):
  try:
   assert f in verified and c['id'].startswith('NEU_') and c['native_bridge_function']==f
   assert c['native_bridge_sha256']==verified[f]['semantic_review_sha256']
   assert not v.predecessor.NEE_validate.suspended_reference(c)
   assert v.inherited.certificate(c,subject,result,reviewed)
   import NEJ_validate
   assert NEJ_validate.call_domain(c,subject,result)
   assert c['physical_interpretation_derivation']==verified[f]['physical_qualification']+'; actual typed call-site carriers, complete native value/Box frame and reached-domain theorems; no callee PhysicalInterpretation assumed'
   assert c['native_association']==verified[f]['support']
   assert c['theorems']==verified[f]['theorems']
   return True
  except (AssertionError,KeyError,TypeError,ValueError,OSError):return False
 for f in verified:
  for r in byfunction[f]:
   for h in r['named_hypotheses']:
    subject=f+'::'+h['name'];c=packet['hypotheses'].get(subject)
    if accepted(c,subject,f):h['discharged_by']=c['id']
   for ob in r['caller_domain_obligations']:
    subject=f+' -> '+ob['callee'] if 'callee' in ob else ob['id']
    c=packet['edges'].get(subject) if 'callee' in ob else packet.get('externals',{}).get(subject)
    if accepted(c,subject,f):ob.update(status='CLOSED',discharged_by=c['id'])
 changed=True
 while changed:
  changed=False
  for f in verified:
   c=packet['roots'].get(f) or packet['members'].get(f)
   if not accepted(c,f,f):continue
   for r in byfunction[f]:
    r['open_transitive_dependencies']=[g for g in r['open_transitive_dependencies'] if any(x['composed_status']!='CLOSED' for x in byfunction[g])]
    if r['composed_status']=='CLOSED':continue
    if r['open_transitive_dependencies']:continue
    if any(not h['discharged_by'] for h in r['named_hypotheses']):continue
    if any(o['status']!='CLOSED' or not o['discharged_by'] for o in r['caller_domain_obligations']):continue
    if any(any(x['composed_status']!='CLOSED' for x in byfunction[g]) for g in r['canonical_callees']):continue
    r.update(composed_status='CLOSED',composed_reason='NEU complete new native bridge, same-call domains and full Result/state/ordered-effects composition '+c['id']);changed=True
 # Every historical gate ran on the immutable original. Check that the new
 # source-evidence layer changes only these enumerated proof/composition fields.
 allowed={'bridge_status','selected_claims','claim_ids','named_hypotheses','caller_domain_obligations','open_transitive_dependencies','composed_status','composed_reason','NEU_native_admission'}
 for got,previous in zip(result['rows'],out['rows']):
  if previous['function'] not in verified:assert got==previous
  else:
   assert {k:w for k,w in got.items() if k not in allowed}=={k:w for k,w in previous.items() if k not in allowed}
   assert got['canonical_callees']==previous['canonical_callees']
   assert len(got['caller_domain_obligations'])==len(previous['caller_domain_obligations'])
   for a,b in zip(got['caller_domain_obligations'],previous['caller_domain_obligations']):
    mutable={'callee_claims','callee_local_status','required_named_hypotheses','status','discharged_by'}
    assert {k:w for k,w in a.items() if k not in mutable}=={k:w for k,w in b.items() if k not in mutable}
   if got['composed_status']=='CLOSED':
    assert got['selected_claims'] and got['bridge_status']=='CLOSED-CONDITIONAL'
    assert not got['open_transitive_dependencies']
    assert all(h['discharged_by'] for h in got['named_hypotheses'])
    assert all(o['status']=='CLOSED' and o['discharged_by'] for o in got['caller_domain_obligations'])
 assert result['trust_rows']==base['trust_rows']
 result['NEU_native_admissions']=dict(verified=sorted(verified),proposed=sorted(additions),classification='new checked native evidence, then call-domain composition; P6/D188 option A reclassification; original baseline immutable')
 return result
