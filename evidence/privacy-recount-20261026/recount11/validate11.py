import json,lzma,hashlib,base64,collections,subprocess
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
rows=json.loads((P/'rows11.json').read_text());old=json.loads((B/'recount10/rows10.json').read_text());t=json.loads((P/'totals.json').read_text());pins=json.loads((P/'pins.json').read_text())
assert len(rows)==len(old)==407 and len({x['id'] for x in rows})==407
restored={'V197','V233','V236'}
for x,y in zip(rows,old):
 assert x['id']==y['id']
 for k,v in y.items():
  if k=='dependency_bucket':assert x['recount10_bucket']==v
  elif x['id'] in restored and k in ['closure_theorem','closure_route']:assert x['recount10_'+k]==v
  else:assert x[k]==v,(x['id'],k)
 assert x['recount11_class']==x['recount10_class']
 assert (x['recount11_status']=='OPEN')==(x['dependency_bucket'] is not None)
 if x['recount11_status']!=y['recount10_status']:assert x['id'] in restored and x['recount11_status']=='CLOSED-ON-CANDIDATE'
assert collections.Counter(x['recount11_status'] for x in rows)==t['statuses']
assert collections.Counter(x['dependency_bucket'] for x in rows if x['recount11_status']=='OPEN')==t['open_dependencies']
assert collections.Counter(x['recount11_class'] for x in rows)==t['classes']
assert collections.Counter(x['in_headline_closure11'] for x in rows)==t['all_row_imports']
assert t['statuses']=={'REDUCED':176,'OPEN':66,'CLOSED-ON-RESEARCH':87,'EVIDENCED':14,'CLOSED-ON-CANDIDATE':64}
assert t['k3_credits']=={'RESTORED':26,'UNAFFECTED':81,'SUSPENDED':195,'WITHDRAWN':3}
finalcredits=json.loads((P/'k3-final-credits11.json').read_text());assert len(finalcredits)==305 and collections.Counter(x['final_status'] for x in finalcredits)==t['k3_credits']
assert t['Lean']==t['Kani']==0 and t['endpoint_premises_removed_added_weakened']==[0,0,0]
assert pins['revisions']['rw']=='d4ed1ba89f05a754d3982b9250f53acbd405ce7b'
assert pins['revisions']['research']=='dc2c38a96fa80321c42b49011af0d76eb909be0e'
definitions=json.loads((P/'definition-audit11.json').read_text());assert len(definitions)==407
assert all(z['path']=='docs/research/v8-r0-zk-20261009/LOG.md' for x in definitions for z in x['changed'])
assert len(json.loads((P/'import-membership11.json').read_text()))==407
m=json.loads((P/'manifest.json').read_text());groups=collections.defaultdict(list)
for x in m:groups[x['snapshot']].append(x)
verified=0
for path,entries in groups.items():
 compressed=(P/path).read_bytes();raw=lzma.decompress(compressed)
 assert hashlib.sha256(raw).hexdigest()==(P/(path+'.sha256')).read_text().strip()
 bundle=json.loads(raw)
 for x in entries:
  v=bundle[x['snapshot_key']];data=v['data'].encode() if v['encoding']=='utf8' else base64.b64decode(v['data'])
  assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256']
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['blob'],(x['ref'],x['path'])
  verified+=1
for name in ['host-native-sources.json','host-timing/inputs.json','client-gate-inputs.json']:
 raw=lzma.decompress((P/(name+'.xz')).read_bytes());assert hashlib.sha256(raw).hexdigest()==(P/(name+'.sha256')).read_text().strip()
source=json.loads((P/'source-binding-audit11.json').read_text());assert source['status']=='PASS'
status=json.loads((P/'status-audit11.json').read_text());assert status['no_new_uninventoried_direct_source_consumer']
audit=json.loads((P/'independent-audit11.json').read_text());assert all(audit[i]['disposition']=='CONFIRM qualified restoration' for i in restored)
assert not audit['composition']['result']['composition_counts'];assert audit['client']['raw_audit']['rows'][0]['reachable_constants']==5280
# All historical K3 packets and new pair statuses are separately recorded.
k3=json.loads((P/'k3-audit11.json').read_text());assert k3['no_current_support_suspended'] and k3['counts']==t['k3_credits']
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_text().split('## Recount 11 2026-11-04 (B)',1)[1];assert 'Recount 1' in ledger and 'Recount 11' in ledger and 'Target not yet established' in ledger
md=(B/'ROWS11.md').read_text();assert sum(line.startswith('|V') for line in md.splitlines())==407
assert 'Target not yet established' in (P/'METHOD11.md').read_text()
files=[p for p in P.rglob('*') if p.is_file() and '__pycache__' not in p.parts];size=sum(p.stat().st_size for p in files)
assert max(p.stat().st_size for p in files)<20*1024*1024
assert size<100*1024*1024,size
assert not any(p.suffix in ['.olean','.elf','.llbc'] for p in files)
changes=subprocess.check_output(['git','diff','--name-only','dc2c38a96fa']).decode().splitlines()
assert all(p.startswith('evidence/privacy-recount-20261026/recount11/') or p in ['evidence/privacy-recount-20261026/ROWS11.md','design/PRIVACY-LEDGER-20261026.md'] for p in changes)
result={'status':'PASS','rows':407,'restored':sorted(restored),'statuses':t['statuses'],'open_dependencies':t['open_dependencies'],'K3':t['k3_credits'],'source_snapshot_records_verified':verified,'lossless_shards_verified':len(groups),'source_git_blob_SHA1_and_SHA256_checked':True,'historical_row_fields_preserved':True,'current_consumer_dispositions':len(status['consumer_dispositions']),'receipt_checks':len(json.loads((P/'receipt-audit11.json').read_text())),'Lean':0,'Kani':0,'Env_J':'92100-92139 unused','evidence_bytes':size,'scope':'source/statement/receipt inspection; no new compiler/solver/audit executions','target':'Target not yet established'}
(P/'validation11.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
