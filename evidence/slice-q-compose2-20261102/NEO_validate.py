#!/usr/bin/env python3
"""Additive checks over the pinned authoritative NEN result.

NEN's successful complete replay is reused with its exact source/output pins.
NEN support denial/coverage functions execute unchanged. New peer assembly has
its own unchanged NEB/NEI gate replay and complete committed input corpus.
No historical suspension is cleared and no missing certificate earns credit.
"""
from pathlib import Path
import sys,json,hashlib,copy,lzma,re,subprocess,base64
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;N=R/'evidence/ledger4-20261102'
sys.path.insert(0,str(N))
import NEN_validate as nen
sha=lambda data:hashlib.sha256(data).hexdigest()
obj=lambda p:json.loads(Path(p).read_text())
require=nen.require
BASE_SHA='cedade116302fea804b3f223a8d889815ef41ebd6f0ea1d5234945fddb89c3ab'
PEER_REV='37638ac1be595801ab9b20957a104bd5126cbb6f'
PEER_ROWS={'TX1:109', 'TX1:114', 'TX1:194', 'TX2:032', 'TX2:101', 'TX1:107', 'TX1:192', 'TX2:120', 'TX1:195', 'TX1:049', 'TX2:080', 'TX1:177', 'TX2:073', 'TX1:115', 'TX2:075', 'TX2:076', 'TX2:081', 'TX2:125', 'TX1:110', 'TX1:106', 'TX2:072', 'TX2:123'}
def baseline():
 raw=(N/'NEN_LEDGER.json').read_bytes();require(sha(raw)==BASE_SHA,'authoritative baseline changed')
 outputs=obj(N/'NEN_OUTPUTS.json')
 for name,pin in outputs.items():
  require(sha((N/name).read_bytes())==pin['sha256'],'changed NEN output: '+name)
 rc=obj(N/'NEN_FINAL.json');require(rc['exit_status']==0,'NEN replay failed')
 for path,digest in rc['source_sha256'].items():require(sha((R/path).read_bytes())==digest,'changed inherited validator: '+path)
 b=json.loads(raw);credits={c['receipt']:c for c in b['NEN_credits']}
 # Additional read-only denial audit; historical accepted records remain intact.
 for row in b['rows']:
  if row['composed_status']!='CLOSED':continue
  require(not nen.support_gate(row['active_support_receipts'],credits),'blocked inherited native support')
  require(not row['open_transitive_dependencies'],'inherited open dependency')
  require(all(h['discharged_by'] for h in row['named_hypotheses']),'inherited open hypothesis')
  require(all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations']),'inherited open call')
 require(nen.coverage(b['rows'])==b['coverage'],'authoritative coverage mismatch')
 return b

def peer_inputs():
 provenance=obj(E/'NEO_NEI_PROVENANCE.json');require(provenance['revision']==PEER_REV,'unreviewed peer revision')
 tree={}
 for line in subprocess.check_output(['git','ls-tree','-rl',PEER_REV,'--',provenance['source_prefix']],cwd=R,text=True).splitlines():
  meta,path=line.split('\t');_,kind,oid,size=meta.split();require(kind=='blob','peer non-blob')
  tree[path]=(oid,int(size))
 require(set(tree)==set(provenance['files']),'peer provenance path inventory differs from Git')
 for path,pin in provenance['files'].items():require((pin['git_blob'],pin['bytes'])==tree[path],'peer Git provenance differs')
 data={}
 for chunk in provenance['archives']:
  raw=(E/chunk['path']).read_bytes();require(len(raw)<20*1024**2,'oversized archive')
  require(sha(raw)==chunk['sha256'],'peer archive drift')
  plain=lzma.decompress(raw);require(sha(plain)==chunk['uncompressed_sha256'],'peer decompression pin')
  current=json.loads(plain);
  if chunk.get('role')!='update':require(not set(data)&set(current),'duplicate peer input')
  data.update(current)
 for path in provenance.get('deleted_paths',[]):data.pop(path,None)
 require(set(data)==set(provenance['files']),'peer input inventory')
 for path,text in data.items():
  raw=text.encode() if isinstance(text,str) else base64.b64decode(text['base64']);require(sha(raw)==provenance['files'][path]['sha256'],'peer input hash: '+path)
  require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==tree[path][0],'peer input differs from committed Git blob')
 return data

def audit_peer(data,packet):
 rc=obj(E/'NEO_PEER_POSITIVE_RECEIPT.json');tests=obj(E/'NEO_PEER_TESTS.json')
 require(rc['exit_status']==tests['exit_status']==0,'peer revalidation did not pass')
 require(rc['source_revision']==tests['source_revision']==PEER_REV,'peer revalidation revision')
 require(obj(E/'NEO_PEER_POSITIVE.json')==packet,'peer assembly capsule drift')
 require(set(r['row'] for r in packet['rows'])==PEER_ROWS,'peer row scope')
 require(set(packet['delta']['composed_rows_closed'])==PEER_ROWS,'peer delta scope')
 require(len(packet['edges'])==8 and packet['delta']['edge_closed']==8,'peer edge scope')
 approved_rows={r['row']:r for r in json.loads(data['evidence/slice-q-mul2-20261101/NEI_DERIVED_LEDGER.json'])['rows'] if r['row'] in PEER_ROWS}
 require({r['row']:r for r in packet['rows']}==approved_rows,'unregistered peer row content')
 approved_edges=json.loads(data['evidence/slice-q-mul2-20261101/NEI_COMPOSE_EDGES.json'])
 require(packet['edges']==[e for e in approved_edges['edges'] if e['status']=='CLOSED'],'unregistered peer edge content')
 require(packet['row_certificates']==approved_edges['row_certificates'],'unregistered peer root recipe')
 require(packet['delta']==json.loads(data['evidence/slice-q-mul2-20261101/NEI_COMPOSE_DELTA.json']),'peer delta differs from replayed committed result')
 # Receipt replay is paired with explicit rule-16 denial, never historical credit.
 packets=json.loads(data['evidence/slice-q-mul2-20261101/NEI_CTOR_PACKETS.json'])+json.loads(data['evidence/slice-q-mul2-20261101/NEI_DOT_FINISH_PACKETS.json'])
 for p in packets:
  require(p['suspended_neb_credits_restored']==[] and p['remaining_inner_hypotheses']==[],'peer hidden credit')
  for attempt in p['native_pair'][:2]:
   prefix='evidence/slice-q-mul2-20261101/'+attempt
   receipt=json.loads(data[prefix+'/receipt.json'])
   # Every original input to this check is present in the archived corpus.
   require(receipt['kind']=='kani','peer native kind')
   for path in receipt['source_hashes']:
    candidates=[k for k in data if k.startswith(prefix+'/') and k.endswith(path)]
    # Native-pair's unchanged gate additionally checks patch/body/graph/KMX pins.
    for name in candidates:
     source=data[name]
     if name.endswith(('.rs','.patch','.rs.txt')):
      require(not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',source),'peer writable static')
 for row in packet['rows']:
  require(row['composed_status']=='CLOSED' and row['bridge_status']=='CLOSED-CONDITIONAL','peer row not composed')
  require(not row['open_transitive_dependencies'],'peer open dependency')
  require(all(h['discharged_by'] for h in row['named_hypotheses']),'peer open hypothesis')
  require(all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations']),'peer open call')

def peer_support(data,function):
 prefix='evidence/slice-q-mul2-20261101/'
 packets=json.loads(data[prefix+'NEI_CTOR_PACKETS.json'])+json.loads(data[prefix+'NEI_GETTER_PACKETS.json'])
 packets += [json.loads(data[prefix+f]) for f in ['NEI_ROW_PACKET.json','NEI_PUSH_PACKET.json','NEI_WIDE_CTOR_PACKET.json']]
 packets += json.loads(data[prefix+'NEI_DOT_FINISH_PACKETS.json'])
 p=next(p for p in packets if p['function']==function)
 support=([p['native_pair'][0]] if 'native_pair' in p else [pair.split('/')[0] for pair in p['new_kani_credits']])
 return [prefix+a+'/receipt.json' for a in support]

def compose(base,peer,edges,parsers=None):
 require(sha(nen.encode(base).encode())==BASE_SHA,'unregistered baseline mutation')
 data=peer_inputs();audit_peer(data,peer)
 import NEO_certificates as own
 registered=own.expected(base,nen.q.check_receipt)
 import NEO_q_certificates as qcert
 qrows,qedges=qcert.expected(base,nen.q.check_receipt)
 import NEO_observer_certificates as ocert
 orows,oedges=ocert.expected(base,nen.q.check_receipt)
 import NEO_getter_certificates as gcert
 grows=gcert.expected(base,nen.q.check_receipt)
 import NEO_getter_edge as gedge
 gedges=gedge.expected(base,nen.q.check_receipt)
 import NEO_cell_certificates as cells
 crows,cedges=cells.expected(base,nen.q.check_receipt)
 import NEO_tail_certificates as tail
 trows,tedges=tail.expected(base,nen.q.check_receipt)
 if parsers is None:parsers=obj(E/'NEO_PARSER_CERTIFICATES.json')
 require(parsers==registered,'unregistered parser certificate')
 old=obj(R/'evidence/slice-q-compose-20261029/NEB_EDGES.json')
 require(set(edges)==set(old)|{'NEO_peer_row_certificates','NEO_baseline','NEO_parser_row_certificates','NEO_q_row_certificates','NEO_observer_row_certificates','NEO_getter_row_certificates','NEO_cell_row_certificates','NEO_tail_row_certificates'},'unexpected edge artifact keys')
 for key in set(old)-{'edges'}:require(edges[key]==old[key],'changed inherited edge artifact field: '+key)
 require(edges['NEO_peer_row_certificates']==peer['row_certificates'],'peer root certificate artifact drift')
 require(edges['NEO_parser_row_certificates']==parsers,'parser root certificate artifact drift')
 require(edges['NEO_q_row_certificates']==qrows,'unregistered private-Q certificate')
 require(edges['NEO_observer_row_certificates']==orows,'unregistered observer certificate')
 require(edges['NEO_getter_row_certificates']==grows,'unregistered borrowed getter certificate')
 require(edges['NEO_cell_row_certificates']==crows,'unregistered cell getter certificate')
 require(edges['NEO_tail_row_certificates']==trows,'unregistered checked-index/opening certificate')
 require(edges['NEO_baseline']=='NEN_LEDGER.json:'+BASE_SHA,'edge baseline pin drift')
 require(len(edges['edges'])==257 and {e['edge'] for e in edges['edges']}=={e['edge'] for e in old['edges']},'slice edge inventory drift')
 byedge={e['edge']:e for e in edges['edges']};new={e['edge']:e for e in peer['edges']}
 for original in old['edges']:
  expected=copy.deepcopy(new.get(original['edge'],original))
  if original['edge'] in qedges:expected.update(qedges[original['edge']])
  if original['edge'] in oedges:expected.update(oedges[original['edge']])
  if original['edge'] in gedges:expected.update(gedges[original['edge']])
  if original['edge'] in cedges:expected.update(cedges[original['edge']])
  if original['edge'] in tedges:expected.update(tedges[original['edge']])
  parser_functions={p['function'] for p in parsers.values()}
  if expected['callee'] in parser_functions:
   if expected['status']!='OPEN':
    require(original['edge'] in new and expected['status']=='CLOSED','new parser refresh shadows an inherited edge certificate')
   else:
    expected['NEO_previous_required_named_hypotheses']=expected['required_named_hypotheses']
    expected['required_named_hypotheses']=['NEO::'+expected['callee']+'.PacketDomain','NEO::'+expected['callee']+'.PhysicalInterpretation']
  require(byedge[original['edge']]==expected,'unregistered edge change')
 out=copy.deepcopy(base);index={r['row']:r for r in out['rows']}
 for r in peer['rows']:
  oldrow=index[r['row']]
  require(oldrow['function']==r['function'] and oldrow['frozen_body_sha256']==r['frozen_body_sha256'],'peer row identity')
  if oldrow['composed_status']=='CLOSED':
   require(r['row'] in {'TX1:115','TX2:081'},'peer shadows a closed row')
   oldrow['NEO_peer_alternative_certificate']=copy.deepcopy(r)
   continue
  require(oldrow['composed_status']=='OPEN','peer shadows a closed row')
  # Preserve the NEN historical record and add the independently replayed row.
  historical=copy.deepcopy(oldrow)
  oldrow.clear();oldrow.update(copy.deepcopy(r))
  support=peer_support(data,r['function'])
  credits={path:dict(receipt=path,k3_status='UNAFFECTED',k2_quarantined=False,reason='Unchanged NEI native-pair gate, rule16 static_declarations=[] and full context/copy controls revalidated') for path in support}
  require(not nen.support_gate(support,credits),'new peer support denied')
  oldrow.update(NEO_NEN_before=historical,NEO_peer_composed_certificate=r,active_support_receipts=support,k3_status='UNAFFECTED',NEO_native_credits=credits,NEO_disposition='Imported committed NEI constructor; unchanged gate replay; no old K-3/K-2 support restored')
  require(all(h['discharged_by'] for h in oldrow['named_hypotheses']),'new row retained an inner hypothesis')
  require(all(o['status']=='CLOSED' and o['discharged_by'] for o in oldrow['caller_domain_obligations']),'new row retained an open call')
 for key,cert in parsers.items():
  if key in PEER_ROWS:
   require(index[key]['function']==cert['function'],'overlapping peer/parser function differs')
   index[key]['NEO_alternative_certificate']=cert
   continue
  row=index[key];require(row['composed_status']=='OPEN' and row['function']==cert['function'],'parser row collision')
  historical=copy.deepcopy(row);identity=cert['id']
  row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=[cert['claim_id']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],composed_reason='New full fixed-input native/reference/Result/carrier/frame packet and all exact external occurrences checked; historical native suspensions retained')
  row['claim_ids']=historical['claim_ids']+[cert['claim_id']]
  row['named_hypotheses']=[dict(name=cert['claim_id']+'.PacketDomain',statement=cert['domain'],discharged_by=identity),dict(name=cert['claim_id']+'.PhysicalInterpretation',statement='Only root source/ABI/tool/std primitive interpretation and P6/D188 semantic transport retained; no inner callee or output-equality premise',discharged_by=identity)]
  for obligation in row['inventory_domain_obligations']:obligation.update(status='CLOSED',discharged_by=identity)
  for obligation in row['caller_domain_obligations']:
   require(obligation['id'] in cert['external_obligations'],'parser external not certified')
   obligation.update(status='CLOSED',discharged_by=identity+':'+obligation['id'])
  support={path:dict(receipt=path,k3_status='UNAFFECTED',k2_quarantined=False,reason='NEO exact fixed-input native pair and KMX controls; no writable static or function pointer') for path in row['active_support_receipts']}
  require(not nen.support_gate(row['active_support_receipts'],support),'parser support denied')
  row['NEO_certificate']=cert;row['NEO_native_credits']=support
  require(all(h['discharged_by'] for h in row['named_hypotheses']),'parser inner hypothesis retained')
  require(all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations']),'parser call left open')
 for key,cert in sorted(qrows.items(),key=lambda item:item[1]['function'].endswith('::checked_q')):
  if key in PEER_ROWS:
   require(index[key]['function']==cert['function'],'overlapping peer/private-Q function differs')
   index[key]['NEO_alternative_Q_certificate']=cert
   continue
  row=index[key];require(row['composed_status']=='OPEN','private-Q row collision')
  for oid,call in cert['calls'].items():
   callee=call['callee'];children=[r for r in out['rows'] if r['function']==callee]
   # Leaf order is explicit below; checked_q comes after the two leaf roots.
   require(children and all(r['composed_status']=='CLOSED' for r in children),'private-Q open callee')
   require(row['function']+' -> '+callee in qedges,'private-Q missing real edge')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=[cert['claim_id']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Full raw private-Q reference/Result/frame with three exact unrestricted callee-domain associations')
  row['named_hypotheses']=[dict(name=cert['claim_id']+'.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['caller_domain_obligations']:
   require(o['id'] in cert['calls'] or o['id'] in cert['external_obligations'],'private-Q missing occurrence')
   o.update(status='CLOSED',discharged_by=cert['id']+':'+o['id'])
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
 for key,cert in orows.items():
  row=index[key];require(row['composed_status']=='OPEN','observer row collision')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::deployed_mark_none'],active_support_receipts=[],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Adopted z(1) exact deployed None specialization and emitted no-effect port; historical function-pointer results remain quarantined')
  row['named_hypotheses']=[dict(name='NEO::deployed_mark_none.PacketDomain',statement=cert['domain'],discharged_by=cert['id'])]
  for o in row['caller_domain_obligations']:
   require(o['id'] in cert['external_obligations'],'observer missing unreachable occurrence')
   o.update(status='CLOSED',discharged_by=cert['id']+':'+o['id'])
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
 for key,cert in grows.items():
  row=index[key];require(row['composed_status']=='OPEN' and not row['caller_domain_obligations'],'getter row collision or unexpected callee')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::geometry_for_query'],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Actual full borrowed getter against independent safe reference, precise same live Vec and emitted carrier/Result/frame; no borrowed contract substitution')
  row['named_hypotheses']=[dict(name='NEO::geometry_for_query.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
 for key,cert in crows.items():
  row=index[key];require(row['composed_status']=='OPEN' and not row['caller_domain_obligations'],'cell row collision or unexpected callee')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::'+cert['function']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Actual indexed scalar/record helper versus independent extracted safe reference, exact coherent op12/op13 and lossless carrier/frame; caller bounds proved')
  row['named_hypotheses']=[dict(name='NEO::'+cert['function']+'.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
 for key,cert in trows.items():
  row=index[key];require(row['composed_status']=='OPEN' and not row['caller_domain_obligations'],'tail row collision or unexpected callee')
  historical=copy.deepcopy(row);row['NEO_NEN_before']=historical
  row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=['NEO::'+cert['function']],active_support_receipts=cert['active_support_receipts'],k3_status='UNAFFECTED',open_transitive_dependencies=[],NEN_rejections=[],NEO_certificate=cert,composed_reason='Actual all-input checked constructor / complete physical opening versus independent extracted reference; exact full Result and same caller carrier/frame')
  row['named_hypotheses']=[dict(name='NEO::'+cert['function']+'.'+kind,statement=cert['domain'],discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
  for o in row['inventory_domain_obligations']:o.update(status='CLOSED',discharged_by=cert['id'])
 require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')
 baseline_closed_rows={r['row'] for r in base['rows'] if r['composed_status']=='CLOSED'}
 added=(PEER_ROWS|set(parsers)|set(qrows)|set(orows)|set(grows)|set(crows)|set(trows))-baseline_closed_rows
 for original in base['rows']:
  if original['composed_status']=='CLOSED':require(all(index[original['row']][k]==value for k,value in original.items()),'changed inherited CLOSED row field')
 delta=dict(schema='NEO-additive-NEN-v1',baseline_sha256=BASE_SHA,baseline_closed=88,newly_closed=sorted(added),new_count=len(added),total_closed=sum(r['composed_status']=='CLOSED' for r in out['rows']),q_closed=sum(r['composed_status']=='CLOSED' and r['function'] in Q for r in out['rows']),roots={r:'OPEN' for r in ROOTS},edge_closed=sum(e['status']=='CLOSED' for e in edges['edges']),edge_total=257,trust='P6/D188 semantic transport retained; reclassification, never removal',authoritative_input_unmodified=True)
 require(delta['total_closed']==130 and delta['q_closed']==108 and delta['edge_closed']==124,'unexpected additive counts')
 return delta

SLICES=obj(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']
Q=set(SLICES['Q']['functions']);ROOTS=set(SLICES['Q']['roots'])
def main():
 peer=obj(E/'NEO_PEER_POSITIVE.json');base=baseline();edges=obj(E/'NEO_EDGES.json')
 delta=compose(base,peer,edges)
 if '--write' in sys.argv:(E/'NEO_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
 else:require(delta==obj(E/'NEO_LEDGER_DELTA.json'),'derived delta drift')
 print(json.dumps(delta))
if __name__=='__main__':main()
