from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for positive,negative in [('NKR_K011','NKR_K004'),('NKR_K007','NKR_K008')]:
 if not (E/negative/'receipt.json').exists():continue
 p=json.loads((E/positive/'receipt.json').read_text());n=json.loads((E/negative/'receipt.json').read_text())
 assert p['exit_status']==0 and n['exit_status']!=0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/positive/'stdout.log').read_text()
 neg=(E/negative/'stdout.log').read_text();assert 'VERIFICATION:- FAILED' in neg and 'CBMC timed out' not in neg
 for a,r in [(positive,p),(negative,n)]:
  assert json.loads((E/(a+'-admission.json')).read_text())['reservation']['allowed'] is True
  g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen']
  assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
  assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_TARGET_DIR'].startswith('/home/dombarker/project-offloads/codex-cx-terminal5-20261108/')
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert p['module']==n['module']
 names=set(p['source_hashes'])&set(n['source_hashes']);names={x for x in names if not re.fullmatch('NKR_K[0-9]{3}.json',x)}
 assert all(p['source_hashes'][x]==n['source_hashes'][x] for x in names)
 rows.append(dict(positive=positive,negative=negative,harness=p['module'],positive_receipt_sha256=sha(E/positive/'receipt.json'),negative_receipt_sha256=sha(E/negative/'receipt.json'),same_input_hashes={x:p['source_hashes'][x] for x in sorted(names)}))
prior=E.parent/'terminal4-20261108/NKI_NATIVE_PAIRS.json';x=json.loads(prior.read_text());assert x['all_pairs_checked']
(E/'NKR_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=rows,predecessor_pairs=dict(path=str(prior),sha256=sha(prior),count=len(x['pairs'])),kmx_patch_sha256=sha(E/'NKR_KMX.patch')),indent=1))
print('Native pairs checked: '+str(len(rows))+'; retained NKI pairs pinned: '+str(len(x['pairs'])))
