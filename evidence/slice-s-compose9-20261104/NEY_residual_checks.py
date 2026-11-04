"""Residual result path: native complete windows, reached domains and AB effects.
No partial set or model-only theorem can promote a native row.
"""
from pathlib import Path
import copy,re,json
import NEY_validate as v
import NEY_bridge_checks as common
E=v.E;R=v.R
P='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'
BIND=P+'validate_pool_v1_pair_forest_terminal_result_against_statement_v1'
ENC=P+'encode_pool_v1_pair_forest_terminal_result_v1'
EMIT='programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result'
FUNCTIONS=[BIND,ENC,EMIT]
PINS={'binding':'20ba9e5605be45bf5d3a79685d49239cc06abc734bc430765676f9d1a7f1922e','encoder':'59a8e0b98e2d3c8de8fc6d6fd26666bf3c2b816f013efb6065bb4c096e38ce37','emission':'97f437d5845081b92097f91fe069d2a215d4110185e7d0ed2f0f419247542675'}
def template(kind):
 data=v.read(E/'NEY_RESIDUAL_TEMPLATE_PINS.json')[kind];assert v.sha(data['source'].encode())==data['source_sha256']==PINS[kind];return data['source']

DOMAINS={BIND:'all typed statements; result is the same statement-derived record',ENC:'ReadyRecord: result derived from a statement whose validator succeeds; established only on the reached encoder branch',EMIT:'all valid typed statements; complete binding and encoder Results; every returning runtime byte/effect'}
THEOREMS={BIND:['NEY_BindingContinuation.result','NEY_BindingSuccess.binding_success','NEY_ReachedResultDomains.binding_argument'],ENC:['NEY_ResultEncoderOracle.result_state_effects','NEY_ResultStores.stores_observe','NEY_ResultProjection.stores_spec','NEY_ResultConstants.layout','NEY_ResultConstants.partition','NEY_ReachedResultDomains.ready_payload'],EMIT:['NEY_EmitComposed.result_state_effects','NEY_EmitComposed.reached_encoder','NEY_ReachedResultDomains.encoder_argument','NEX_ReturnData.set_preserves_order','NEX_ReturnData.runtime_bound','NEX_ReturnData.observable']}

def native(a,positive,function):
 m=v.read(E/(a+'-shape.json'));snap=v.native(a,positive);cfg=v.read(E/(a+'.json'));cmd=cfg['native_command']
 harness={BIND:'pool_v1::pair_forest_terminal::NEY_binding::binding',ENC:'pool_v1::pair_forest_terminal::NEY_result_parent::result_parent',EMIT:'r1_pool_adapter::NEY_emit_parent::emit_parent'}[function]
 assert cfg['module']==harness and cmd[cmd.index('--harness')+1]==harness and '--exact' in cmd
 assert cmd[cmd.index('--features')+1]==cfg.get('program_features',cfg['statement_features'])
 assert m['source'] in ''.join(l[1:]+'\n' for l in snap['NEY_native_contracts.patch'].splitlines() if l.startswith('+') and not l.startswith('+++'))
 frozen=v.inherited.inherited.frozen_source(function);name=function.rsplit('::',1)[1]
 marker=('fn ' if function==EMIT else 'pub fn ')+name+'(';start=frozen.index(marker);end=frozen.index('\n}',start)+2
 assert m['frozen_body']==frozen[start:end]
 assert not re.search(r'\b(?:static|transmute|UnsafeCell|RefCell|Cell)\b',m['source'])
 return m

def binding(config):
 assert config=={'positive':'NEY_K109','value':'NEY_K110'}
 base=None
 for mode,a in config.items():
  m=native(a,mode=='positive',BIND);assert m['mode']==mode
  text=m['native'].replace('fn native(','pub fn validate_pool_v1_pair_forest_terminal_result_against_statement_v1(').replace('    result: &PoolV1PairForestTerminalResultV1,f:&mut Frame,','    result: &PoolV1PairForestTerminalResultV1,')
  text=common.undo(text,'check_statement','validate_pool_v1_pair_forest_terminal_statement_v1');text=common.undo(text,'check_result','validate_result');assert text==m['frozen_body']
  for token in ['core::ptr::eq(s,f.s)','core::ptr::eq(r,f.r)','frame.calls==1','frame.calls==2','transition_kind:s.transition_kind()','master_account:c.master_account','selected_lane_account:c.selected_lane_account','output_lane:c.output_lane','nullifier:*s.nullifier()','verified_afterstate:c.lane_transition.candidate_afterstate']:
   assert token in m['source'],token
  if mode=='positive':
   assert m['source']==template('binding')
   base=m['source']
  elif mode=='value':assert m['source']==base.replace('assert!(out==expected);','assert!(out==expected.map(|_|()).and(Err(PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch)));')
  else:assert m['source']==base.replace('};\nlet first','};r.master_account[0]^=1;\nlet first')
 return True

def encoder(config):
 assert len(config)==9
 starts=[0,4,5,6,7,8,40,72,104];sizes=[4,1,1,1,1,32,32,32,688]
 values=['POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[j]','POOL_V1_PAIR_FOREST_TERMINAL_VERSION','r.transition_kind as u8','POOL_V1_DIGEST_ENCODING_VERSION','r.output_lane','r.master_account[j-8]','r.selected_lane_account[j-40]','d[j-72]','after_bytes[j-104]']
 for slot,pair in enumerate(config):
  assert pair==[f'NEY_K{111+slot*2:03}',f'NEY_K{112+slot*2:03}']
  base=None
  for mode,a in zip(['positive','value'],pair):
   m=native(a,mode=='positive',ENC);assert m['slot']==slot and m['mode']==mode and m['start']==starts[slot] and m['size']==sizes[slot]
   text=m['native'].replace('fn native(','pub fn encode_pool_v1_pair_forest_terminal_result_v1(').replace('    result: &PoolV1PairForestTerminalResultV1,f:&mut Frame,','    result: &PoolV1PairForestTerminalResultV1,')
   for new,old in [('validate','validate_result'),('digest','encode_digest_canonical'),('after','encode_pool_v1_pair_verified_afterstate_v1')]:text=common.undo(text,new,old)
   assert text==m['frozen_body']
   for token in ['core::ptr::eq(r,f.record)','core::ptr::eq(d,&f.record.nullifier)','core::ptr::eq(a,&f.record.verified_afterstate)','frame.calls==1','frame.calls==3','Err(NEE_any_PoolV1PairVerifierTransportErrorV1())',f'kani::assume({starts[slot]}<=j&&j<{starts[slot]+sizes[slot]})']:
    assert token in m['source'],token
   assertion=f'assert!(b[j]==({values[slot]})'+('^1' if mode=='value' else '')+');'
   assert assertion in m['source']
   if mode=='positive':
    expected=template('encoder').replace('kani::assume(0<=j&&j<4)',f'kani::assume({starts[slot]}<=j&&j<{starts[slot]+sizes[slot]})').replace('assert!(b[j]==(POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[j]));',f'assert!(b[j]==({values[slot]}));')
    assert m['source']==expected
    base=m['source']
   else:assert m['source']==base.replace(f'assert!(b[j]==({values[slot]}));',assertion)
 return True

def emission(config):
 assert config=={'positive':'NEY_K129','byte':'NEY_K130','order':'NEY_K131','argument':'NEY_K132'}
 base=None
 for mode,a in config.items():
  m=native(a,mode=='positive',EMIT);assert m['mode']==mode
  text=m['native'].replace('fn native(statement: &PoolV1PairForestTerminalStatementV1,f:&mut Frame) -> ProgramResult','fn emit_result(statement: &PoolV1PairForestTerminalStatementV1) -> ProgramResult')
  for new,old in [('binding','validate_pool_v1_pair_forest_terminal_result_against_statement_v1'),('encode','encode_pool_v1_pair_forest_terminal_result_v1'),('send','program::set_return_data')]:text=common.undo(text,new,old)
  if mode=='argument':text=text.replace('program::set_return_data(&encoded[1..])','program::set_return_data(&encoded)')
  assert text==m['frozen_body']
  for token in ['core::ptr::eq(s,f.s)','core::ptr::eq(r,f.record)','f.calls==2&&bytes.len()==792','f.sent=Some(bytes[f.j])','frame.sent==None','raw[0]==65&&raw[1]==83&&raw[2]==82&&raw[3]==56','frame.calls==1','frame.calls==2']:
   assert token in m['source'],token
  if mode=='positive':
   assert m['source']==template('emission')
   base=m['source']
  elif mode=='byte':assert m['source']==base.replace('Some(raw[j])','Some(raw[j]^1)')
  elif mode=='order':assert m['source']==base.replace('frame.calls==3&&frame.sent','frame.calls==2&&frame.sent')
  else:assert m['source']==base.replace('send(&encoded,f)','send(&encoded[1..],f)')
 # No later setter exists after the one frozen call; no Unit-erased event.
 original=m['frozen_body'];assert original.count('program::set_return_data')==1
 assert original[original.index('program::set_return_data'):].strip()=='program::set_return_data(&encoded);\n    Ok(())\n}'
 return True

def classify(function,callee):
 if function in [BIND,EMIT] and (callee.endswith('::PoolV1PairForestTerminalPaymentV1::nullifier') or callee.endswith('::PoolV1PairForestTerminalPaymentV1::transition_kind') or callee==P+'transition_kind'):
  return 'alternative-resolution: concrete Statement receiver, not Payment; no free transition_kind call'
 return 'reached same typed argument, closed callee domain and physical carrier'

def check(c,base):
 n=c['native_certificate'];f=n['function'];assert f in FUNCTIONS and c['subject']==f
 assert c['kind']==('root-composition' if f==EMIT else 'member-composition') and n['complete'] is True
 assert n['domain']==DOMAINS[f] and n['inner_hypotheses_remaining']==[]
 assert c['hypotheses']==[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA']+(['RuntimeReturnData'] if f==EMIT else [])
 assert c['new_trust_rows']==(['RuntimeReturnData'] if f==EMIT else [])
 assert c['addition_classification']==('ADDED runtime trust under ruling(ab)' if f==EMIT else 'none')
 assert [t['name'] for t in c['domain_theorems']]==THEOREMS[f] and c['physical_theorems']==c['domain_theorems']
 {BIND:binding,ENC:encoder,EMIT:emission}[f](n['config'])
 by={}
 for row in base['rows']:by.setdefault(row['function'],[]).append(row)
 expected=[o['id'] for row in by[f] for o in row['caller_domain_obligations']]
 assert c['required_obligations']==expected
 assert set(c['edges'])=={edge for edge in common.SPEC['internal_edges'] if edge.startswith(f+' -> ')}
 assert set(c['call_domain_certificates'])==set(c['edges'])
 for edge,d in c['call_domain_certificates'].items():
  caller,g=edge.split(' -> ');assert caller==f and d['subject']==edge
  names={h['name'] for r in by[g] for h in r['named_hypotheses']}|{h for r in by[f] for o in r['caller_domain_obligations'] if o.get('callee')==g for h in o['required_named_hypotheses']}
  assert set(d['inner_names_discharged'])==names
  assert set(d['selected_callee_claims'])=={x for r in by[g] for x in r['selected_claims']} and d['selected_callee_claims']
  assert d['classification']==classify(f,g) and d['inner_hypotheses_remaining']==[]
  assert d['domain_theorems']==c['domain_theorems'] and d['physical_theorems']==c['physical_theorems']
  for key in ['same_arguments','same_prestate','same_result','same_ordered_effects','canonical_carrier','callee_domain_established','native_frame_complete']:assert d[key] is True
  if d['classification'].startswith('alternative-resolution'):
   original=v.inherited.inherited.frozen_source(f);name=f.rsplit('::',1)[1];start=original.index(('fn ' if f==EMIT else 'pub fn ')+name+'(');text=original[start:original.index('\n}',start)+2]
   assert 'statement: &PoolV1PairForestTerminalStatementV1' in text and 'PoolV1PairForestTerminalPaymentV1' not in text
   assert not re.search(r'(?<![\w.:])transition_kind\s*\(',text)
 attempts=list(n['config'].values()) if f!=ENC else [a for pair in n['config'] for a in pair]
 expected_support={str((E/'NEY_RESIDUAL_TEMPLATE_PINS.json').relative_to(R))}
 for a in attempts:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEY_native_contracts.patch',a+'-NEY_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEY_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256']
  expected_support.update(str((E/name).relative_to(R)) for name in names)
 if f==EMIT:
  for a in ['NEU_K003','NEU_K004']:
   folder=E.parent/'slice-s-compose7-20261103'
   names=[a+'/receipt.json',a+'/stdout.log',a+'.json','NEU_K004-emit.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEU_native_contracts.patch',a+'-NEU_oracle.patch']
   archive=a+'-inputs.json' if (folder/(a+'-inputs.json.xz')).exists() else 'NEU_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256']
   expected_support.update(str((folder/name).relative_to(R)) for name in names)
  import NEU_bridge_checks
  assert NEU_bridge_checks.native_pair(v.inherited.inherited,['NEU_K003','NEU_K004'])
 assert {ref['path'] for ref in c['support']}==expected_support
 assert c['inner_hypotheses_remaining']==[]
 return True

def compose(base,result,packet,api):
 by={}
 for row in result['rows']:by.setdefault(row['function'],[]).append(row)
 for f in FUNCTIONS:
  c=packet.get('NEY_certificates',{}).get(f)
  if not api.certificate(c,f,result):continue
  if any(any(r['composed_status']!='CLOSED' for r in by[g]) for row in by[f] for g in row['canonical_callees']):continue
  for row in by[f]:
   row['bridge_status']='CLOSED-CONDITIONAL';row['selected_claims']=['NEY::'+f];row['claim_ids']=list(dict.fromkeys(row['claim_ids']+['NEY::'+f]))
   known={h['name'] for h in row['named_hypotheses']}
   for name in [f+'.PacketDomain',f+'.PhysicalInterpretation']:
    if name not in known:row['named_hypotheses'].append(dict(name=name,statement=DOMAINS[f] if name.endswith('.PacketDomain') else 'Valid native/cohort typed carrier, ABI, allocator and approved P6 tool interpretation',discharged_by=None))
   for h in row['named_hypotheses']:h['discharged_by']=c['id']+'::'+h['name']
   for ob in row['caller_domain_obligations']:
    if 'callee' in ob:
     d=c['call_domain_certificates'][f+' -> '+ob['callee']];ob['callee_claims']=list(dict.fromkeys(ob['callee_claims']+d['selected_callee_claims']));ob['required_named_hypotheses']=list(dict.fromkeys(ob['required_named_hypotheses']+d['inner_names_discharged']))
    ob.update(status='CLOSED',discharged_by=c['id']+'::'+ob['id'])
   row['open_transitive_dependencies']=[g for g in row['open_transitive_dependencies'] if any(r['composed_status']!='CLOSED' for r in by[g])]
   if not row['open_transitive_dependencies']:row.update(composed_status='CLOSED',composed_reason='NEY complete native result path, reached derived/ready domains, KMX store/window composition and closed children'+('; RuntimeReturnData ADDED under ab' if f==EMIT else ''))
  if f==EMIT:result['NEY_added_runtime_trust_rows']=[dict(id='RuntimeReturnData',classification='ADDED runtime trust under ruling(ab)',scope='same-instruction no-intervening-CPI set/get returns exact program id and bytes; Pool immediate read/program-id check remains a separate caller obligation')]
 return result
