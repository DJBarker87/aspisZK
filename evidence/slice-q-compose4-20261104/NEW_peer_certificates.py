"""Import only the two newly composed peer rows, preserving inherited rows."""
from NEW_inverse_checks import *
import copy
ACC='crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node'
REV='577526934d2472c6910f88f45c93ce9bb3631b2a'
def expected(base,prior):
 pins=obj(E/'NEW_PEER_IMPORT_PINS.json');assert pins['revision']==REV
 for name,h in pins['files'].items():assert sha(E/name)==h,('peer replay artifact drift',name)
 receipt=obj(E/'NEW_PEER_NEV_REPLAY_RECEIPT.json');assert receipt['exit_status']==0 and receipt['source_revision']==REV and receipt['swaps']==0
 m=obj(E/'NEW_PEER_NEV_ARCHIVE.json');assert m['revision']==REV
 z=b''
 for item in m['parts']:
  b=(E/item['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==item['sha256'];z+=b
 assert hashlib.sha256(z).hexdigest()==m['compressed_sha256']
 raw=lzma.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['raw_sha256'];pack=json.loads(raw);assert pack['revision']==REV
 def data(name):
  item=pack['blobs'][pack['files']['evidence/slice-q-mul3-20261103/'+name]['blob']]
  assert item['encoding']=='utf8';b=item['content'].encode();assert hashlib.sha256(b).hexdigest()==item['sha256'];return json.loads(b)
 ledger=data('NEV_DERIVED_LEDGER.json');edges=data('NEV_EDGES.json');certs=data('NEV_UNION_CERTIFICATES.json')
 checked=obj(E/'NEW_PEER_NEV_CHECKED.json');assert checked['unchanged_peer_checks'] is True and checked['archive_raw_sha256']==m['raw_sha256']
 rows=[r for r in ledger['rows'] if r['function']==ACC];assert {r['row']for r in rows}=={'TX1:182','TX2:108'}
 source_edges=[e for e in edges['edges']if e['caller']==ACC]
 assert rows==checked['rows_data'] and source_edges==checked['edges'] and certs['rows']==checked['row_certificates']
 byrow={r['row']:r for r in base['rows']};byedge={e['edge']:e for e in prior['edges']};out=[];new_edges={}
 provenance=dict(revision=REV,archive='NEW_PEER_NEV_ARCHIVE.json',raw_sha256=m['raw_sha256'],unchanged_gate_receipt='NEW_PEER_NEV_REPLAY_RECEIPT.json',receipt_sha256=sha(E/'NEW_PEER_NEV_REPLAY_RECEIPT.json'))
 for row in rows:
  assert row['composed_status']=='CLOSED' and not row['open_transitive_dependencies']
  assert row['frozen_body_sha256']==byrow[row['row']]['frozen_body_sha256']
  assert all(o['status']=='CLOSED'for o in row['caller_domain_obligations']+row['inventory_domain_obligations'])
  assert all(h['discharged_by']for h in row['named_hypotheses'])
  cert=certs['rows'][row['row']];assert cert['remaining_inner_hypotheses']==[] and cert['function']==ACC
  assert cert['parts']==['result','state','ordered_effects','native_association']
  out.append(dict(id='NEW-peer-accum:'+row['row'],row=row['row'],function=ACC,domain=cert['domain'],parts=cert['parts'],remaining_inner_hypotheses=[],original_certificate=cert,original_composed_row=row,import_provenance=provenance))
 for edge in source_edges:
  old=byedge[edge['edge']];assert old['caller']==ACC
  if old['status']=='CLOSED':
   assert old.get('selected_target')==edge.get('selected_target')
   continue
  assert old['status']=='OPEN'
  for key in ['edge','obligation_id','source_body_sha256','caller','callee']:assert edge[key]==old[key]
  assert edge['status']=='CLOSED' and not edge['certificate']['residual_hypotheses']
  replacement=copy.deepcopy(edge);replacement['NEW_import_provenance']=provenance;new_edges[edge['edge']]=replacement
 assert source_edges and len(new_edges)==len(source_edges)-2
 return out,new_edges
