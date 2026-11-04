"""Only the four newly reviewed fold rows; no wholesale peer ledger promotion."""
from NET_window_certificates import *
import base64
KEEP={'TX1:188','TX1:190','TX2:113','TX2:117'}
REV='5d12713bd3d7b813a911201357b22e2ef2d5acfa'
def peer_inputs():
 p=obj(E/'NET_NEI_PROVENANCE.json');assert p['revision']==REV
 files={}
 for a in p['archives']:
  raw=(E/a['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==a['sha256']
  plain=lzma.decompress(raw);assert hashlib.sha256(plain).hexdigest()==a['uncompressed_sha256']
  files.update(json.loads(plain))
 for name in p['deleted_paths']:files.pop(name,None)
 assert set(files)==set(p['files'])
 for name,value in files.items():
  raw=value.encode() if isinstance(value,str) else base64.b64decode(value['base64'])
  assert hashlib.sha256(raw).hexdigest()==p['files'][name]['sha256']
  assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==p['files'][name]['git_blob']
 return p,files

def expected(base):
 p,data=peer_inputs();rc=obj(E/'NET_PEER_POSITIVE_RECEIPT.json')
 assert rc['exit_status']==0 and rc['source_revision']==REV and rc['prover_runs']==0
 packet=obj(E/'NET_PEER_POSITIVE.json')
 committed=json.loads(data[p['source_prefix']+'NEI_DERIVED_LEDGER.json']);calls=json.loads(data[p['source_prefix']+'NEI_COMPOSE_EDGES.json'])
 rows=[r for r in committed['rows'] if r['row'] in KEEP]
 recipes=[r for r in calls['row_certificates'] if r['row'] in KEEP]
 assert len(rows)==len(recipes)==4
 assert {r['row']:r for r in packet['rows'] if r['row'] in KEEP}=={r['row']:r for r in rows}
 assert {r['row']:r for r in packet['row_certificates'] if r['row'] in KEEP}=={r['row']:r for r in recipes}
 functions={r['function'] for r in rows}
 edges={e['edge']:e for e in calls['edges'] if e['caller'] in functions and e['status']=='CLOSED'}
 assert len(edges)==30 and edges=={e['edge']:e for e in packet['edges'] if e['caller'] in functions}
 for row in rows:
  assert row['composed_status']=='CLOSED' and not row['open_transitive_dependencies']
  assert all(x['discharged_by'] for x in row['named_hypotheses'])
  assert all(x['status']=='CLOSED' and x['discharged_by'] for x in row['caller_domain_obligations'])
 for recipe in recipes:
  assert recipe['remaining_inner_hypotheses']==[] and set(recipe['parts'])=={'result','state','ordered_effects','native_association'}
  for item in recipe['lean_evidence']:
   raw=data[item['receipt']];assert hashlib.sha256(raw.encode()).hexdigest()==item['receipt_sha256']
   proof=json.loads(raw);assert proof['exit_status']==0 and proof['limits']==CAPS and int(proof['swaps'])==0
   for theorem in item['theorems']:
    lines=[s for s in proof['print_axioms'] if s.startswith("'"+theorem+"'")];assert len(lines)==1
    if 'does not depend on any axioms' in lines[0]:continue
    m=re.search(r'axioms: \[([^]]*)\]',lines[0]);assert m
    assert {a.strip() for a in m[1].split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
 # Receipt, full source-tree Git pins and exact committed recipes jointly bind
 # the replay. WIP ancestors and all unselected peer rows retain no NET credit.
 return rows,recipes,edges
