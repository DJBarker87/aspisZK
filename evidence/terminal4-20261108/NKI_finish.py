from pathlib import Path
import json,hashlib,collections,subprocess,re
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g=load('NKI_AUDIT_ROOTS.json');wanted=set(g['roots']);results=[];groups=[]
classifications={x['attempt']:x for x in [json.loads(l)for l in(E/'NKI_RAW_CLASSIFICATIONS.jsonl').read_text().splitlines()]}
for i,expected in enumerate(g['groups']):
 r=load(f'NKI_audit/proof{i}/receipt.json');assert r['standard_only']
 if r['exit_status']:
  c=classifications[r['scope_attempt']];assert r['exit_status']==1 and c['accepted'] and c['classification']=='AX2_STANDARD_RAW_COLLECTOR_TOOLING_FINDING' and c['receipt_sha256']==sha(E/f'NKI_audit/proof{i}/receipt.json')
 actual=[x['root'] for x in r['results']];assert len(actual)==len(set(actual)) and set(actual)==set(expected),(i,len(actual),len(expected))
 for x in r['results']:assert set(x['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}
 results.extend(r['results']);groups.append(dict(group=i,roots=len(actual),original_exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],collect_axioms_disagreements=len(r['collect_axioms_disagreements'])))
assert len(results)==len(wanted)==len(set(x['root']for x in results))
assert set(x['root']for x in results)==wanted and set(g['new_roots'])<=wanted
scan=load('NKI_audit/scan/receipt.json');assert scan['exit_status']==0 and not(scan['dangling']or scan['duplicate_owners']or scan['import_mismatch'])
assert load('NKI_audit/fixtures/receipt.json')['fixture_pass']
assert load('NKI_WALKER_PINS.json')['byte_identical']
assert load('NKI_L090/receipt.json')['exit_status']==0
pairs=load('NKI_NATIVE_PAIRS.json');assert pairs['all_pairs_checked'] and len(pairs['pairs'])==44
attempts=[json.loads(l)for l in(E/'NKI_ATTEMPTS.jsonl').read_text().splitlines()]
counts=collections.Counter(x['attempt'][4]for x in attempts);assert counts['L']==120 and counts['K']==11
assert len({x['attempt']for x in attempts})==len(attempts)
for a in attempts:
 ad=load(a['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
 rc=load(a['attempt']+'/receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert rc['source_revision'] and rc['source_hashes'] and rc['wall_seconds']>=0

assert load('NKI_L121/receipt.json')['exit_status']==0
sources=load('NKI_GATE_SOURCES.json')
# Gate input hashes were frozen before first combined import.
for mod,item in sources['passed'].items():
 assert sha(E/(mod+'.lean'))==load(item+'/receipt.json')['source_hashes'][mod+'.lean']
for a in attempts:
 if a['attempt'] in ['NKI_L090','NKI_L091','NKI_L092'] or 93<=int(a['attempt'][-3:])<=120 and a['attempt'][4]=='L':
  rc=load(a['attempt']+'/receipt.json');assert str(rc['swaps'])=='0'
  if rc['exit_status']:assert rc['exit_status']==1 and classifications[a['attempt']]['accepted']
assert load('NKI_EXPORT.json')['retained']
import base64,lzma
artifact_count=0
for q in (E/'NKI_audit').rglob('*.xz.b64.txt'):
 raw=lzma.decompress(base64.b64decode(q.read_bytes()))
 expected=(q.parent/(q.name.removesuffix('.xz.b64.txt')+'.sha256')).read_text().strip()
 assert hashlib.sha256(raw).hexdigest()==expected,q
 artifact_count+=1
raw_disagreements=[x['root']for x in results if not x['equal']]
row=dict(status='PASS_NEXT_LEDGER_GATE',target_established=False,authoritative_delta=0,candidate_rows=['TX1:234','TX1:235','TX1:260','TX1:233'],headline='AspisR1.RPx_Deployed.deployed',combined_import_attempt='NKI_L090',full_combined_audits=1,fixtures_attempt='NKI_L091',fixtures_pass=True,scan_attempt='NKI_L092',scan={k:scan[k]for k in ['modules','dangling','duplicate_owners','import_mismatch','exit_status','wall_seconds','peak_rss_kib','swaps']},raw_root_count=len(results),new_root_count=len(g['new_roots']),raw_groups=groups,standard_axioms_only=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],collect_axioms_disagreements=raw_disagreements,ax2='raw walk authoritative; all collector disagreements retained in group receipts',native_pairs_revalidated=44,compressed_raw_artifacts_hash_verified=artifact_count,usage=dict(lean_support=counts['L'],kani=counts['K'],extraction=0,lean_limit=120,kani_limit=70),under80percent_reason='All120 Lean/support scopes consumed; member-by-member remaining native-plus-Lean, external225/308 and adoption obligations in NKI_REMAINING.md. Unused Kani alone cannot discharge these.',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_hash_manifest='NKI_GATE_SOURCES.json',retained_export='NKI_EXPORT.json',CARGO_TARGET_DIR=load('NKI_EXPORT.json')['CARGO_TARGET_DIR'])
(E/'NKI_AUDIT.json').write_text(json.dumps(row,indent=1))
c=load('NKI_CLOSED.json')
for f in c['functions']:f['local_gate']='PASS_NEXT_LEDGER_GATE'
(E/'NKI_CLOSED.json').write_text(json.dumps(c,indent=1))
d=load('NKI_LEDGER_DELTA.json');d['local_gate']='PASS_NEXT_LEDGER_GATE';d['authoritative_delta']=0
(E/'NKI_LEDGER_DELTA.json').write_text(json.dumps(d,indent=1))
for q in E.rglob('*'):
 if q.is_file():assert q.stat().st_size<=20_000_000,q
print(json.dumps(dict(status=row['status'],roots=len(results),groups=len(groups),usage=row['usage'],disagreements=len(raw_disagreements))))
