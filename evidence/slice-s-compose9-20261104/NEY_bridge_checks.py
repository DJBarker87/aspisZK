"""Complete return-field admission; no credit from partial field collections."""
import json,re,difflib,copy
from pathlib import Path
import NEY_validate as v
E=v.E;R=v.R
P='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'
TERMINAL=P+'decode_pool_v1_pair_forest_terminal_statement_v1'
PUBLIC='programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box'
SPEC=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices']['S']
EXPECTED=json.loads((E.parent/'slice-s-compose8-20261104/NEX_K133-shape.json').read_text())
assert v.sha((E.parent/'slice-s-compose8-20261104/NEX_K133-shape.json').read_bytes())=='1553be2e5c13209142e4a3bc0279b8cb51b45b9a44c174993d6712c6e5d7c9d3'

PUBLIC_SOURCE_SHA256='d65e600f14b62b4f14eebbc304414f28abaed3ba91b900aa2dc132be9324a3ce'
TERMINAL_SOURCE_SHA256='e83ce3210af08c40390103d4ff53d4d6b2bbbb4519bff904d854ce166c4f407e'

def undo(text,new,old):
 # Reverse only the exact source-checked call redirection, preserving argument
 # expressions and order; the local record is the sole ghost parameter.
 from NEX_raw_checks import undo_call
 return undo_call(text,new,old)

def attempt(a,slot,mode,family):
 m=v.read(E/(a+'-shape.json'))
 assert m['field_slot']==slot and m['mode']==mode and m['full_child_Result'] is True
 snapshots=v.native(a,mode=='positive');source=m['source'];f=TERMINAL if family=='terminal' else PUBLIC
 cfg=v.read(E/(a+'.json'));command=cfg['native_command']
 harness='pool_v1::pair_forest_terminal::NEY_terminal::terminal' if family=='terminal' else 'r1_pool_adapter::NEY_public::public'
 assert cfg['module']==harness and command[command.index('--harness')+1]==harness and '--exact' in command
 assert '--no-default-features' not in command
 assert command[command.index('--features')+1]==cfg.get('program_features',cfg['statement_features'])
 assert 'Checking harness '+harness in (E/a/'stdout.log').read_text()
 assert m['fields']==[EXPECTED['fields'][slot]]
 assert 'fn project(' in source and EXPECTED['fields'][slot] in source
 assert 'slot<1&&i<8&&j<32&&k<20' in source if family=='terminal' else 'i<8&&j<32&&k<20' in source
 frozen=v.inherited.inherited.frozen_source(f);name=f.rsplit('::',1)[1]
 marker=('pub fn ' if family=='terminal' else 'fn ')+name+'('
 start=frozen.index(marker);end=frozen.index('\n}',start)+2
 assert m['frozen_body']==frozen[start:end]
 text=m['native'].replace('fn native(',marker).replace('    bytes: &[u8],f:&mut Frame,','    bytes: &[u8],')
 if family=='terminal':
  baseline=v.read(E/'NEY_K001-shape.json')['source']
  assert v.sha(baseline.encode())==TERMINAL_SOURCE_SHA256
  baseline=baseline.replace('0=>'+EXPECTED['fields'][0], '0=>'+EXPECTED['fields'][slot])
  if mode=='value':
   baseline=baseline.replace('project(&expected,slot,i,j,k))','project(&expected,slot,i,j,k)^1)')
   if slot>=23:
    variant='PrivateTransfer' if slot==23 else 'Withdrawal'
    baseline=baseline.replace('let v=if kani::any()',f'kani::assume(matches!(s,Ok(PoolV1PairForestTerminalStatementV1::{variant}{{..}})));let v=if kani::any()')
  assert source==baseline, 'source not the independently reviewed single-field template'
  for new,old in [('common','decode_terminal_common_boxed_v1'),('transfer','decode_transfer_statement_boxed_v1'),('withdrawal','decode_withdrawal_statement_boxed_v1'),('validate','validate_pool_v1_pair_forest_terminal_statement_v1')]:text=undo(text,new,old)
  assert text==m['frozen_body']
  for expr in ['bytes.len()==1880','bytes.len()==216','f.bytes[1664..].as_ptr()','kind==f.bytes[5]','core::ptr::eq(&*common,f.common_place)','core::ptr::eq(s,f.statement_place)','f.calls==3','f.v','f.s.map','f.c.map','Ok(*statement)']:
   assert expr in source,expr
 else:
  baseline=v.read(E/'NEY_K054-shape.json')['source'];assert v.sha(baseline.encode())==PUBLIC_SOURCE_SHA256
  project='fn project(s:&PoolV1PairForestTerminalStatementV1,slot:usize,i:usize,j:usize,k:usize)->u64{'
  baseline=baseline.replace(project+EXPECTED['fields'][0]+'}',project+EXPECTED['fields'][slot]+'}')
  if mode=='value':
   baseline=baseline.replace('project(&expected,slot,i,j,k))','project(&expected,slot,i,j,k)^1)')
   if slot>=23:
    variant='PrivateTransfer' if slot==23 else 'Withdrawal'
    baseline=baseline.replace('let mut f=Frame',f'kani::assume(matches!(reply,Ok(PoolV1PairForestTerminalStatementV1::{variant}{{..}})));let mut f=Frame')
  assert source==baseline
  text=undo(text,'decode','decode_pool_v1_pair_forest_terminal_statement_v1')
  text=text.replace('let out=Box::new(','Ok(Box::new(').replace('    );\n    f.allocated=&*out;\n    Ok(out)','    ))')
  if mode=='allocation':text=text.replace('Ok(Box::new(*out))','Ok(out)')
  assert text==m['frozen_body']
  for expr in ['bytes.len()==f.bytes.len()','core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr())','f.calls==1','core::ptr::eq(&*out,f.allocated)','f.allocated.is_null()','Err(ProgramError::InvalidAccountData)']:
   assert expr in source,expr
 patch=snapshots['NEY_native_contracts.patch']
 assert source in ''.join(l[1:]+'\n' for l in patch.splitlines() if l.startswith('+') and not l.startswith('+++'))
 if mode=='value':
  assert 'FailedChecks:assertionfailed:project(&out,slot,i,j,k)==project(&expected,slot,i,j,k)^1' in re.sub(r'\s+','',(E/a/'stdout.log').read_text())
 assert f'project(&expected,slot,i,j,k){"^1" if mode=="value" else ""}' in source
 return m

def check(c,base):
 n=c['native_certificate'];f=n['function'];assert f in [TERMINAL,PUBLIC]
 assert c['subject']==f
 assert c['kind']==('root-composition' if f==PUBLIC else 'member-composition')
 family='terminal' if f==TERMINAL else 'public'
 assert n['complete'] is True and n['inner_hypotheses_remaining']==[]
 expected_geometry=['NEY_TerminalGeometry.'+name for name in ['payment_offset','header_constants','kind_same','payment_window']] if family=='terminal' else []
 assert [t['name'] for t in c['geometry_theorems']]==expected_geometry
 import NED_validate
 assert all(NED_validate.theorem(t) for t in c['geometry_theorems'])
 assert n['length_partition']==(['NEX_K130','NEX_K131'] if family=='terminal' else [])
 inherited_support=set()
 if family=='terminal':
  for a,positive in [('NEX_K130',True),('NEX_K131',False)]:
   snapshots=v.inherited.native(a,positive);folder=v.inherited.E;m=v.read(folder/(a+'-shape.json'))
   assert m['mode']==('positive' if positive else 'negative')
   assert m['frozen_prefix']==EXPECTED['frozen_body'][:EXPECTED['frozen_body'].index('    if bytes[..4]')]
   width='1880' if positive else '1881'
   expected='''use super::*;
fn length_gate(length:usize)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{if length!=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);}Ok(())}
#[kani::proof]
fn length_gate_all(){let length:usize=kani::any();assert!(length_gate(length)==if length=='''+width+'''{Ok(())}else{Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)});}
'''
   assert m['source']==expected
   assert expected in ''.join(l[1:]+'\n' for l in snapshots['NEX_native_contracts.patch'].splitlines() if l.startswith('+') and not l.startswith('+++'))
   cfg=v.read(folder/(a+'.json'));assert cfg['module']=='pool_v1::pair_forest_terminal::NEX_length::length_gate_all'
   assert cfg['native_command'][cfg['native_command'].index('--harness')+1]==cfg['module']
   names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEX_native_contracts.patch',a+'-NEX_oracle.patch']
   archive=a+'-inputs.json' if (folder/(a+'-inputs.json.xz')).exists() else 'NEX_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256']
   inherited_support.update(str((folder/name).relative_to(R)) for name in names)
 assert n['controls']==(['NEY_K053'] if family=='terminal' else ['NEY_K106','NEY_K107'])
 for a in n['controls']:
  m=v.read(E/(a+'-shape.json'));snapshots=v.native(a,False)
  cfg=v.read(E/(a+'.json'));command=cfg['native_command'];harness='pool_v1::pair_forest_terminal::NEY_terminal::terminal' if family=='terminal' else 'r1_pool_adapter::NEY_public::public'
  assert cfg['module']==harness and command[command.index('--harness')+1]==harness
  assert m['source'] in ''.join(l[1:]+'\n' for l in snapshots['NEY_native_contracts.patch'].splitlines() if l.startswith('+') and not l.startswith('+++'))
  assert m['mode']=={'NEY_K053':'argument','NEY_K106':'allocation','NEY_K107':'reply'}[a]
  assert m['frozen_body']==EXPECTED['frozen_body'] if family=='terminal' else m['frozen_body']==v.read(E/'NEY_K054-shape.json')['frozen_body']
  if family=='terminal':
   expected=v.read(E/'NEY_K001-shape.json')['source'].replace('bytes[PAYMENT_STATEMENT_OFFSET..]','bytes[PAYMENT_STATEMENT_OFFSET+1..]')
  elif a=='NEY_K106':expected=v.read(E/'NEY_K054-shape.json')['source'].replace('    f.allocated=&*out;\n    Ok(out)','    f.allocated=&*out;\n    Ok(Box::new(*out))')
  else:expected=v.read(E/'NEY_K056-shape.json')['source'].replace('f.calls=1;f.reply','f.calls=1;f.reply.map(|mut s|{match &mut s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,..}|PoolV1PairForestTerminalStatementV1::Withdrawal{common,..}=>common.master_account[0]^=1};s})')
  assert m['source']==expected

 assert len(n['pairs'])==26
 for slot,pair in enumerate(n['pairs']):
  assert len(pair)==2
  for a,mode in zip(pair,['positive','value']):attempt(a,slot,mode,family)
 assert [t['name'] for t in c['domain_theorems']]==([
 'NEX_TerminalOracle.result_state_effects','NEX_TerminalDomain.wrong_length','NEX_TerminalDomain.fixed_carrier','NEX_DecoderDomains.common_windows','NEX_StatementExt.complete','NEU_DecoderProjections.payment_packet'] if f==TERMINAL else ['NEX_PublicModel.result_state_effects','NEX_StatementExt.complete'])+[f'NEY_Field{slot:02}.alignment' for slot in range(26)]
 assert c['physical_theorems']==c['domain_theorems']
 table=v.read(v.inherited.artifact(c['field_alignment_table']))
 assert len(table)==26
 for slot,row in enumerate(table):
  assert row['slot']==slot and row['native_projection']==EXPECTED['fields'][slot]
  t=c['domain_theorems'][-26+slot]
  assert t['name']==f'NEY_Field{slot:02}.alignment'
  source=v.inherited.artifact(t['source']).read_text()
  assert f'⟨{slot},by decide⟩' in t['statement']
  assert '| .PrivateTransfer c p => '+row['transfer'] in source
  assert '| .Withdrawal c p => '+row['withdrawal'] in source

 expected_support=set(inherited_support)
 for a in [a for pair in n['pairs'] for a in pair]+n['controls']:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEY_native_contracts.patch',a+'-NEY_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEY_SOURCE_HISTORY.json'
  names += [archive+'.xz',archive+'.sha256']
  expected_support.update(str((E/name).relative_to(R)) for name in names)
 assert {pin['path'] for pin in c['support']}==expected_support

 assert c['required_obligations']==[o['id'] for r in base['rows'] if r['function']==f for o in r['caller_domain_obligations']]
 assert set(c['edges'])=={edge for edge in SPEC['internal_edges'] if edge.startswith(f+' -> ')}
 by={}
 for row in base['rows']:by.setdefault(row['function'],[]).append(row)
 assert set(c['call_domain_certificates'])==set(c['edges'])
 for edge,d in c['call_domain_certificates'].items():
  caller,callee=edge.split(' -> ');assert caller==f and d['subject']==edge
  obs=[o for r in by[caller] for o in r['caller_domain_obligations'] if o.get('callee')==callee]
  names=set(h for o in obs for h in o.get('required_named_hypotheses',[]))|{h['name'] for r in by[callee] for h in r['named_hypotheses']}
  claims={claim for r in by[callee] for claim in r['selected_claims']}
  assert names==set(d['inner_names_discharged']) and claims==set(d['selected_callee_claims']) and claims
  assert d['domain_theorems']==c['domain_theorems'] and d['physical_theorems']==c['physical_theorems']
  assert d['inner_hypotheses_remaining']==[] and d['trust_classification']==c['trust_classification']
  for key in ['same_arguments','same_prestate','same_result','same_ordered_effects','canonical_carrier','callee_domain_established','native_frame_complete']:assert d[key] is True
 assert c['hypotheses']==[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA']
 assert c['new_trust_rows']==[]
 return True

def compose_additions(base,result,packet,api):
 by={}
 for row in result['rows']:by.setdefault(row['function'],[]).append(row)
 for f in [TERMINAL,PUBLIC]:
  c=packet.get('NEY_certificates',{}).get(f)
  if not api.certificate(c,f,result):continue
  rows=by[f]
  # Never discharge a native child by assuming its domain at the root.
  if any(any(q['composed_status']!='CLOSED' for q in by[g]) for row in rows for g in row['canonical_callees']):continue
  for row in rows:
   row['bridge_status']='CLOSED-CONDITIONAL';row['selected_claims']=['NEY::'+f]
   row['claim_ids']=list(dict.fromkeys(row['claim_ids']+['NEY::'+f]))
   known={h['name'] for h in row['named_hypotheses']}
   for name in [f+'.PacketDomain',f+'.PhysicalInterpretation']:
    if name not in known:row['named_hypotheses'].append(dict(name=name,statement='Root-owned valid immutable typed Slice; full native length partition and approved physical/ABI/allocator/P6 interpretation',discharged_by=None))
   # Retain each old name; its concrete call-domain derivation is part of the
   # same complete certificate, never a newly assumed child premise.
   for h in row['named_hypotheses']:h['discharged_by']=c['id']+'::'+h['name']
   for ob in row['caller_domain_obligations']:
    if 'callee' in ob:
     d=c['call_domain_certificates'][f+' -> '+ob['callee']]
     ob['callee_claims']=list(dict.fromkeys(ob['callee_claims']+d['selected_callee_claims']))
     ob['required_named_hypotheses']=list(dict.fromkeys(ob['required_named_hypotheses']+d['inner_names_discharged']))
    ob.update(status='CLOSED',discharged_by=c['id']+'::'+ob['id'])
   row['open_transitive_dependencies']=[g for g in row['open_transitive_dependencies'] if any(q['composed_status']!='CLOSED' for q in by[g])]
   if not row['open_transitive_dependencies']:row.update(composed_status='CLOSED',composed_reason='NEY all26 independent native fields, complete Results, call places/order, inherited model/domain/extensionality and closed children')
 allowed={'bridge_status','selected_claims','claim_ids','named_hypotheses','caller_domain_obligations','open_transitive_dependencies','composed_status','composed_reason'}
 for a,b in zip(result['rows'],base['rows']):
  assert {k:w for k,w in a.items() if k not in allowed}=={k:w for k,w in b.items() if k not in allowed}
 return result
