"""Data integrity and scope checks only; never launches Lean/Kani/builds."""
import json,lzma,base64,hashlib,collections,subprocess
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
rows=json.loads((P/'rows10.json').read_text());old=json.loads((B/'recount9/rows9.json').read_text());t=json.loads((P/'totals.json').read_text());pins=json.loads((P/'pins.json').read_text());m=json.loads((P/'manifest.json').read_text())
assert len(rows)==len(old)==407 and [r['id'] for r in rows]==[r['id'] for r in old]
changed=[]
for r,o in zip(rows,old):
 for k,v in o.items():
  if k in ['dependency_bucket','closure_theorem','closure_route']:continue
  assert r[k]==v,(r['id'],k)
 if r['recount9_status']!=r['recount10_status']:changed.append(r['id'])
 assert r['recount10_class']==r['recount9_class']
 if r['recount10_status']=='OPEN':assert r['dependency_bucket'] in 'abcd'
 else:assert r['dependency_bucket'] is None
membership=json.loads((P/'import-membership10.json').read_text());assert [x['id'] for x in membership]==[r['id'] for r in rows]
assert all(r['import_witnesses10']=='import-membership10.json#'+r['id'] for r in rows)
assert changed==['V201','V220','V237','V242']
assert t['statuses']==dict(collections.Counter(r['recount10_status'] for r in rows))
assert t['open_dependencies']==dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount10_status']=='OPEN'))
assert t['statuses']['OPEN']==69 and t['statuses']['CLOSED-ON-CANDIDATE']==61
assert t['classes']=={'P':400,'C':4,'T':3}
assert t['endpoint_premises_removed_added_weakened']==[0,0,0]
assert t['Lean']==t['Kani']==pins['budget']['used_Lean']==pins['budget']['used_Kani']==0
assert pins['budget']['env_J']=='90300-90399' and not pins['budget']['consumed_IDs']
assert pins['revisions']['rw'].startswith('ba1fa07d9e') and pins['revisions']['research'].startswith('a6138b93b9')
by={r['id']:r for r in rows};assert by['V244']['recount10_status']=='OPEN'
k=json.loads((P/'k3-audit10.json').read_text());assert len(k['rows'])==34
assert k['counts']=={'SUSPENDED':199,'UNAFFECTED':81,'RESTORED':22,'WITHDRAWN':3}
assert all(not q['depends_on_still_suspended_credit'] for q in k['rows'])
assert not any(c['positive_exit'] or c['control_exit']==0 for c in k['pairs'])
a=json.loads((P/'independent-audit10.json').read_text());assert a['D565']['NDR_authority']=='INCOHERENT, excluded'
assert a['measured']['Core_byte_identical_to_adoption'] and len(a['measured']['forwarded_runtime_fields'])==22
assert len(a['consumers']['remaining'])==7 and a['consumers']['counted_rows_removed']==0
# Each compressed shard and every original snapshot gets a byte-for-byte check.
index={}
for f in sorted((P/'bundles').glob('*.json.xz')):
 raw=lzma.decompress(f.read_bytes());assert hashlib.sha256(raw).hexdigest()==Path(str(f)+'.sha256').read_text().strip()
 for h,x in json.loads(raw).items():
  b=x['data'].encode() if x['encoding']=='utf8' else base64.b64decode(x['data']);assert hashlib.sha256(b).hexdigest()==h
  index[(str(f.relative_to(P)),h)]=(h,len(b))
for x in m:assert index[x['snapshot'],x['snapshot_key']]==(x['sha256'],x['bytes'])
defs=json.loads((P/'definition-audit10.json').read_text());assert len(defs)==407
assert all(s['path'].endswith('/LOG.md') for r in defs for s in r['changed'])
extra=json.loads((P/'supplemental10.json').read_text());assert len(extra)==8
assert {r['id'] for r in defs if not r['sources']}=={r['id'] for r in extra}
manifest_keys={(x['ref'],x['revision'],x['path'],x['sha256']) for x in m}
for r in defs:
 for x in r['sources']:assert (x['ref'],x['revision'],x['path'],x['sha256']) in manifest_keys
s=Path('design/PRIVACY-LEDGER-20261026.md').read_text();base=subprocess.check_output(['git','show',pins['revisions']['research']+':design/PRIVACY-LEDGER-20261026.md'],text=True)
assert s.startswith(base) and s.count('## Recount 10 2026-11-02 (B)')==1
append=s[len(base):];assert '| OPEN | 138 | 110 | 103 | 95 | 93 | 86 | 77 | 81 | 73 | 69 |' in append
assert '| CLOSED-ON-CANDIDATE | 13 | 40 | 27 | 35 | 37 | 44 | 53 | 49 | 57 | 61 |' in append
assert 'Target not yet established' in append
assert len([l for l in (B/'ROWS10.md').read_text().splitlines() if l.startswith('|V')])==407
files=[f for f in P.rglob('*') if f.is_file()];total=sum(f.stat().st_size for f in files)
assert not [str(f) for f in files if f.stat().st_size>20_000_000]
assert total<100*1024*1024,total
paths=subprocess.check_output(['git','diff','--name-only'],text=True).splitlines();assert all(x=='design/PRIVACY-LEDGER-20261026.md' or x.startswith('evidence/privacy-recount-20261026/recount10/') for x in paths),paths
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-recount10-20261102'
result={'status':'PASS','rows':407,'status_changes':changed,'totals':t['statuses'],'exclusive_open_buckets':t['open_dependencies'],'snapshot_records':len(m),'distinct_snapshot_bytes_checked':len(index),'k3_rows':34,'controlled_pairs_checked':len(k['pairs']),'Lean_invocations':0,'Kani_invocations':0,'new_proofs':0,'bytes':total,'no_Stream_A_or_source_edits':True,'ledger_append_only':True,'release_or_raw_joint_audit_claimed':False,'target':'Target not yet established'}
(P/'validation10.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
