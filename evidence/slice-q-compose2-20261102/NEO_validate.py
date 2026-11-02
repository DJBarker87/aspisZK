#!/usr/bin/env python3
"""Additive checks over the pinned authoritative NEN result.

NEN's successful complete replay is reused with its exact source/output pins.
NEN support denial/coverage functions execute unchanged. New peer assembly has
its own unchanged NEB/NEI gate replay and complete committed input corpus.
No historical suspension is cleared and no missing certificate earns credit.
"""
from pathlib import Path
import sys,json,hashlib,copy,lzma,re,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;N=R/'evidence/ledger4-20261102'
sys.path.insert(0,str(N))
import NEN_validate as nen
sha=lambda data:hashlib.sha256(data).hexdigest()
obj=lambda p:json.loads(Path(p).read_text())
require=nen.require
BASE_SHA='cedade116302fea804b3f223a8d889815ef41ebd6f0ea1d5234945fddb89c3ab'
PEER_REV='66c32b92421564a57aa9b98547b3bafbbe88a304'
PEER_ROWS={'TX1:107','TX1:110','TX2:073','TX2:076'}
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
  current=json.loads(plain);require(not set(data)&set(current),'duplicate peer input');data.update(current)
 require(set(data)==set(provenance['files']),'peer input inventory')
 for path,text in data.items():
  raw=text.encode();require(sha(raw)==provenance['files'][path]['sha256'],'peer input hash: '+path)
  require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==tree[path][0],'peer input differs from committed Git blob')
 return data

def audit_peer(data,packet):
 rc=obj(E/'NEO_PEER_POSITIVE_RECEIPT.json');tests=obj(E/'NEO_PEER_TESTS.json')
 require(rc['exit_status']==tests['exit_status']==0,'peer revalidation did not pass')
 require(rc['source_revision']==tests['source_revision']==PEER_REV,'peer revalidation revision')
 require(obj(E/'NEO_PEER_POSITIVE.json')==packet,'peer assembly capsule drift')
 require(set(r['row'] for r in packet['rows'])==PEER_ROWS,'peer row scope')
 require(set(packet['delta']['composed_rows_closed'])==PEER_ROWS,'peer delta scope')
 require(len(packet['edges'])==1 and packet['delta']['edge_closed']==1,'peer edge scope')
 approved_rows={r['row']:r for r in json.loads(data['evidence/slice-q-mul2-20261101/NEI_DERIVED_LEDGER.json'])['rows'] if r['row'] in PEER_ROWS}
 require({r['row']:r for r in packet['rows']}==approved_rows,'unregistered peer row content')
 approved_edges=json.loads(data['evidence/slice-q-mul2-20261101/NEI_COMPOSE_EDGES.json'])
 require(packet['edges']==[e for e in approved_edges['edges'] if e['status']=='CLOSED'],'unregistered peer edge content')
 require(packet['row_certificates']==approved_edges['row_certificates'],'unregistered peer root recipe')
 require(packet['delta']==json.loads(data['evidence/slice-q-mul2-20261101/NEI_COMPOSE_DELTA.json']),'peer delta differs from replayed committed result')
 # Receipt replay is paired with explicit rule-16 denial, never historical credit.
 packets=json.loads(data['evidence/slice-q-mul2-20261101/NEI_CTOR_PACKETS.json'])
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

def compose(base,peer,edges,parsers=None):
 require(sha(nen.encode(base).encode())==BASE_SHA,'unregistered baseline mutation')
 data=peer_inputs();audit_peer(data,peer)
 import NEO_certificates as own
 registered=own.expected(base,nen.q.check_receipt)
 if parsers is None:parsers=obj(E/'NEO_PARSER_CERTIFICATES.json')
 require(parsers==registered,'unregistered parser certificate')
 old=obj(R/'evidence/slice-q-compose-20261029/NEB_EDGES.json')
 require(set(edges)==set(old)|{'NEO_peer_row_certificates','NEO_baseline','NEO_parser_row_certificates'},'unexpected edge artifact keys')
 for key in set(old)-{'edges'}:require(edges[key]==old[key],'changed inherited edge artifact field: '+key)
 require(edges['NEO_peer_row_certificates']==peer['row_certificates'],'peer root certificate artifact drift')
 require(edges['NEO_parser_row_certificates']==parsers,'parser root certificate artifact drift')
 require(edges['NEO_baseline']=='NEN_LEDGER.json:'+BASE_SHA,'edge baseline pin drift')
 require(len(edges['edges'])==257 and {e['edge'] for e in edges['edges']}=={e['edge'] for e in old['edges']},'slice edge inventory drift')
 byedge={e['edge']:e for e in edges['edges']};new={e['edge']:e for e in peer['edges']}
 for original in old['edges']:
  expected=copy.deepcopy(new.get(original['edge'],original))
  parser_functions={p['function'] for p in parsers.values()}
  if expected['callee'] in parser_functions:
   require(expected['status']=='OPEN','new parser refresh shadows an inherited edge certificate')
   expected['NEO_previous_required_named_hypotheses']=expected['required_named_hypotheses']
   expected['required_named_hypotheses']=['NEO::'+expected['callee']+'.PacketDomain','NEO::'+expected['callee']+'.PhysicalInterpretation']
  require(byedge[original['edge']]==expected,'unregistered edge change')
 out=copy.deepcopy(base);index={r['row']:r for r in out['rows']}
 for r in peer['rows']:
  oldrow=index[r['row']]
  require(oldrow['function']==r['function'] and oldrow['frozen_body_sha256']==r['frozen_body_sha256'],'peer row identity')
  require(oldrow['composed_status']=='OPEN','peer shadows a closed row')
  # Preserve the NEN historical record and add the independently replayed row.
  historical=copy.deepcopy(oldrow)
  oldrow.clear();oldrow.update(copy.deepcopy(r))
  support=['evidence/slice-q-mul2-20261101/NEI_K021/receipt.json']
  if r['function'].endswith('::EbyKDot::new'):support.append('evidence/slice-q-mul2-20261101/NEI_K023/receipt.json')
  credits={path:dict(receipt=path,k3_status='UNAFFECTED',k2_quarantined=False,reason='Unchanged NEI native-pair gate, rule16 static_declarations=[] and full context/copy controls revalidated') for path in support}
  require(not nen.support_gate(support,credits),'new peer support denied')
  oldrow.update(NEO_NEN_before=historical,NEO_peer_composed_certificate=r,active_support_receipts=support,k3_status='UNAFFECTED',NEO_native_credits=credits,NEO_disposition='Imported committed NEI constructor; unchanged gate replay; no old K-3/K-2 support restored')
  require(all(h['discharged_by'] for h in oldrow['named_hypotheses']),'new row retained an inner hypothesis')
  require(all(o['status']=='CLOSED' and o['discharged_by'] for o in oldrow['caller_domain_obligations']),'new row retained an open call')
 for key,cert in parsers.items():
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
 require(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function'] in ROOTS),'root accidentally closed')
 delta=dict(schema='NEO-additive-NEN-v1',baseline_sha256=BASE_SHA,baseline_closed=88,newly_closed=sorted(PEER_ROWS|set(parsers)),new_count=len(PEER_ROWS|set(parsers)),total_closed=sum(r['composed_status']=='CLOSED' for r in out['rows']),q_closed=sum(r['composed_status']=='CLOSED' and r['function'] in Q for r in out['rows']),roots={r:'OPEN' for r in ROOTS},edge_closed=sum(e['status']=='CLOSED' for e in edges['edges']),edge_total=257,trust='P6/D188 semantic transport retained; reclassification, never removal',authoritative_input_unmodified=True)
 require(delta['total_closed']==96 and delta['q_closed']==74 and delta['edge_closed']==108,'unexpected additive counts')
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
