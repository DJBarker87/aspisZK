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
  if mode=='value':baseline=baseline.replace('project(&expected,slot,i,j,k))','project(&expected,slot,i,j,k)^1)')
  assert source==baseline, 'source not the independently reviewed single-field template'
  for new,old in [('common','decode_terminal_common_boxed_v1'),('transfer','decode_transfer_statement_boxed_v1'),('withdrawal','decode_withdrawal_statement_boxed_v1'),('validate','validate_pool_v1_pair_forest_terminal_statement_v1')]:text=undo(text,new,old)
  assert text==m['frozen_body']
  for expr in ['bytes.len()==1880','bytes.len()==216','f.bytes[1664..].as_ptr()','kind==f.bytes[5]','core::ptr::eq(&*common,f.common_place)','core::ptr::eq(s,f.statement_place)','f.calls==3','f.v','f.s.map','f.c.map','Ok(*statement)']:
   assert expr in source,expr
 else:
  text=undo(text,'decode','decode_pool_v1_pair_forest_terminal_statement_v1')
  text=text.replace('let out=Box::new(','Ok(Box::new(').replace('    );\n    f.allocated=&*out;\n    Ok(out)','    ))')
  if mode=='allocation':text=text.replace('Ok(Box::new(*out))','Ok(out)')
  assert text==m['frozen_body']
  for expr in ['bytes.len()==f.bytes.len()','core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr())','f.calls==1','core::ptr::eq(&*out,f.allocated)','f.allocated.is_null()','Err(ProgramError::InvalidAccountData)']:
   assert expr in source,expr
 patch=snapshots['NEY_native_contracts.patch']
 assert source in ''.join(l[1:]+'\n' for l in patch.splitlines() if l.startswith('+') and not l.startswith('+++'))
 assert f'project(&expected,slot,i,j,k){"^1" if mode=="value" else ""}' in source
 return m

def check(c,base):
 n=c['native_certificate'];f=n['function'];assert f in [TERMINAL,PUBLIC]
 family='terminal' if f==TERMINAL else 'public'
 assert n['complete'] is True and n['inner_hypotheses_remaining']==[]
 assert n['controls']==(['NEY_K053'] if family=='terminal' else ['NEY_K106','NEY_K107'])
 for a in n['controls']:
  m=v.read(E/(a+'-shape.json'));v.native(a,False)
  assert m['mode']=={'NEY_K053':'argument','NEY_K106':'allocation','NEY_K107':'reply'}[a]
  assert m['frozen_body']==EXPECTED['frozen_body'] if family=='terminal' else m['frozen_body']==v.read(E/'NEY_K054-shape.json')['frozen_body']
  if family=='terminal':assert 'PAYMENT_STATEMENT_OFFSET+1' in m['native']
  elif a=='NEY_K106':assert 'Ok(Box::new(*out))' in m['native']
  else:assert 'common.master_account[0]^=1' in m['source']
 assert len(n['pairs'])==26
 for slot,pair in enumerate(n['pairs']):
  assert len(pair)==2
  for a,mode in zip(pair,['positive','value']):attempt(a,slot,mode,family)
 assert [t['name'] for t in c['domain_theorems']]==([
 'NEX_TerminalOracle.result_state_effects','NEX_TerminalDomain.wrong_length','NEX_TerminalDomain.fixed_carrier','NEX_DecoderDomains.common_windows','NEX_StatementExt.complete','NEU_DecoderProjections.payment_packet'] if f==TERMINAL else ['NEX_PublicModel.result_state_effects','NEX_StatementExt.complete'])
 assert c['physical_theorems']==c['domain_theorems']
 assert c['required_obligations']==[o['id'] for r in base['rows'] if r['function']==f for o in r['caller_domain_obligations']]
 assert set(c['edges'])=={edge for edge in SPEC['internal_edges'] if edge.startswith(f+' -> ')}
 assert c['hypotheses']==[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA']
 assert c['new_trust_rows']==[]
 return True

def compose_additions(base,result,packet,api):
 by={}
 for row in result['rows']:by.setdefault(row['function'],[]).append(row)
 for f in [TERMINAL,PUBLIC]:
  c=packet.get('NEY_certificates',{}).get(f)
  if not api.certificate(c,f,base):continue
  rows=by[f]
  # Never discharge a native child by assuming its domain at the root.
  if any(any(q['composed_status']!='CLOSED' for q in by[g]) for row in rows for g in row['canonical_callees']):continue
  for row in rows:
   row['bridge_status']='CLOSED-CONDITIONAL';row['selected_claims']=['NEY::'+f]
   row['claim_ids']=list(dict.fromkeys(row['claim_ids']+['NEY::'+f]))
   # Retain each old name; its concrete call-domain derivation is part of the
   # same complete certificate, never a newly assumed child premise.
   for h in row['named_hypotheses']:h['discharged_by']=c['id']+'::'+h['name']
   for ob in row['caller_domain_obligations']:ob.update(status='CLOSED',discharged_by=c['id']+'::'+ob['id'])
   row['open_transitive_dependencies']=[g for g in row['open_transitive_dependencies'] if any(q['composed_status']!='CLOSED' for q in by[g])]
   if not row['open_transitive_dependencies']:row.update(composed_status='CLOSED',composed_reason='NEY all26 independent native fields, complete Results, call places/order, inherited model/domain/extensionality and closed children')
 allowed={'bridge_status','selected_claims','claim_ids','named_hypotheses','caller_domain_obligations','open_transitive_dependencies','composed_status','composed_reason'}
 for a,b in zip(result['rows'],base['rows']):
  assert {k:w for k,w in a.items() if k not in allowed}=={k:w for k,w in b.items() if k not in allowed}
 return result
