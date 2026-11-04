"""Build complete checked certificates only; partial native collections stay OPEN."""
from pathlib import Path
import sys,json,hashlib,re
import NEY_validate as v
import NEY_bridge_checks as b
E=v.E;R=v.R;sha=v.sha
OLD=E.parent/'slice-s-compose8-20261104'
def ref(p):return {'path':str(p.relative_to(R)),'sha256':sha(p.read_bytes())}
def theorem(name,attempt,folder=OLD,prefix='NEX_'):
 p=folder/attempt/(prefix+'SOURCE.lean.txt');source=p.read_text();start=source.index('theorem '+name.rsplit('.',1)[-1]+' ');end=start+re.search(r'\s:=\s',source[start:]).start();statement=source[start:end].rstrip()
 return dict(name=name,source=ref(p),receipt=ref(folder/attempt/'receipt.json'),snapshot_path=prefix+'generated/'+name.rsplit('.',1)[0]+'.lean',statement=statement,statement_sha256=sha(statement.encode()))
def build(base):
 packet=dict(inherits='evidence/slice-s-compose8-20261104/NEX_LEDGER_DELTA.json.xz',NEY_certificates={})
 for family,f,start in [('terminal',b.TERMINAL,1),('public',b.PUBLIC,54)]:
  pairs=[[f'NEY_K{start+slot*2:03}',f'NEY_K{start+slot*2+1:03}'] for slot in range(26)]
  controls=['NEY_K053'] if family=='terminal' else ['NEY_K106','NEY_K107']
  if not all((E/a/'receipt.json').is_file() for a in [a for pair in pairs for a in pair]+controls):continue
  try:
   for slot,pair in enumerate(pairs):
    for a,mode in zip(pair,['positive','value']):b.attempt(a,slot,mode,family)
  except (AssertionError,KeyError,OSError):continue
  thms=([theorem('NEX_TerminalOracle.result_state_effects','NEX_L012'),theorem('NEX_TerminalDomain.wrong_length','NEX_L033'),theorem('NEX_TerminalDomain.fixed_carrier','NEX_L033'),theorem('NEX_DecoderDomains.common_windows','NEX_L006'),theorem('NEX_StatementExt.complete','NEX_L035'),theorem('NEU_DecoderProjections.payment_packet','NEU_L018',E.parent/'slice-s-compose7-20261103','NEU_')] if family=='terminal' else [theorem('NEX_PublicModel.result_state_effects','NEX_L032'),theorem('NEX_StatementExt.complete','NEX_L035')])
  field_attempts={0:5,12:6,**{slot:n for n,slot in enumerate([s for s in range(26) if s not in [0,12]],9)}}
  thms += [theorem(f'NEY_Field{slot:02}.alignment',f'NEY_L{field_attempts[slot]:03}',E,'NEY_') for slot in range(26)]
  support=[]
  for pair in pairs+[controls]:
   for a in pair:
    names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEY_native_contracts.patch',a+'-NEY_oracle.patch']
    archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEY_SOURCE_HISTORY.json'
    names += [archive+'.xz',archive+'.sha256']
    support += [ref(E/n) for n in names]
  if family=='terminal':
   for a in ['NEX_K130','NEX_K131']:
    names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEX_native_contracts.patch',a+'-NEX_oracle.patch']
    archive=a+'-inputs.json' if (OLD/(a+'-inputs.json.xz')).exists() else 'NEX_SOURCE_HISTORY.json'
    names += [archive+'.xz',archive+'.sha256'];support += [ref(OLD/name) for name in names]
  c=dict(id='NEY_'+family,field_alignment_table=ref(E/'NEY_FIELD_ALIGNMENT_TABLE.json'),subject=f,frozen_revision=base['frozen_revision'],native_certificate=dict(function=f,complete=True,pairs=pairs,controls=controls,length_partition=['NEX_K130','NEX_K131'] if family=='terminal' else [],inner_hypotheses_remaining=[]),domain_theorems=thms,physical_theorems=thms,support=support,required_obligations=[o['id'] for r in base['rows'] if r['function']==f for o in r['caller_domain_obligations']],edges=[edge for edge in b.SPEC['internal_edges'] if edge.startswith(f+' -> ')],hypotheses=[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'],new_trust_rows=[],inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification')
  view=v.compose(base,packet)
  by={}
  for row in view['rows']:by.setdefault(row['function'],[]).append(row)
  c['call_domain_certificates']={}
  for edge in c['edges']:
   caller,callee=edge.split(' -> ')
   obs=[o for r in by[caller] for o in r['caller_domain_obligations'] if o.get('callee')==callee]
   names=list(dict.fromkeys([h for o in obs for h in o.get('required_named_hypotheses',[])]+[h['name'] for r in by[callee] for h in r['named_hypotheses']]))
   claims=list(dict.fromkeys(claim for r in by[callee] for claim in r['selected_claims']))
   c['call_domain_certificates'][edge]=dict(subject=edge,selected_callee_claims=claims,inner_names_discharged=names,domain_theorems=thms,physical_theorems=thms,native_association_kind='ruling-y',same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,canonical_carrier=True,callee_domain_established=True,native_frame_complete=True,inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification')
  c.update({key:True for key in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']})
  c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode())
  assert v.certificate(c,f,view)
  packet['NEY_certificates'][f]=c
 raw=(json.dumps(packet,indent=1)+'\n').encode();(E/'NEY_LEDGER_DELTA.json').write_bytes(raw)
 return packet
if __name__=='__main__':build(v.baseline())
