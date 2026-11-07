from pathlib import Path
import json,hashlib,lzma,collections
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
a=[json.loads(l) for l in (E/'NND_ATTEMPTS.jsonl').read_text().splitlines()]
formal=[r for r in a if r['attempt'].startswith('NND_L') and 'exit_status' in r]
extract=[r for r in a if r['attempt'].startswith('NND_E') and 'exit_status' in r]
assert len(formal)==300 and len(extract)==2
assert len({r['attempt'] for r in formal})==300
assert not any(r.get('kind')=='kani' for r in a)
for r in formal+extract:
 p=E/r['attempt']/'receipt.json';x=json.loads(p.read_text())
 assert x['exit_status']==r['exit_status']
 if 'deps_fingerprint_ref' in r:assert sha(p.read_bytes())==r['deps_fingerprint_ref']['sha256']
 for stem in ['stdout','time']:
  p=E/r['attempt']/(stem+'.log.xz')
  if p.exists():assert sha(lzma.decompress(p.read_bytes()))==(p.with_suffix('.sha256')).read_text().strip()
inputs=json.loads((E/'NND_INPUTS.json').read_text())
for h,x in inputs['objects'].items():
 p=E/x['path'];assert sha(p.read_bytes())==x['archive_sha256'];assert sha(lzma.decompress(p.read_bytes()))==h
modules=json.loads((E/'NND_CURRENT_MODULES.json').read_text())
for m,x in modules.items():assert sha((E/(m+'.lean')).read_bytes())==x['source_sha256']
manifest=json.loads((E/'NND_AUDIT_ROOTS.json').read_text());expected=[n for g in manifest['groups'] for n in g]
rows=[];disagreements=[]
for i in range(len(manifest['groups'])):
 paths=[p for p in E.glob('NND_L*/NND_RAW_AUDIT.json') if json.loads(p.read_text())['mode']=='proof'+str(i)]
 assert len(paths)==1
 x=json.loads(paths[0].read_text());rows.extend(x['roots']);disagreements.extend(x['cache_disagreements'])
assert [r['root'] for r in rows]==expected and len(expected)==314
assert all(set(r['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'} for r in rows)
assert json.loads((E/'NND_L058/NND_RETENTION.json').read_text())['status']=='PASS'
assert json.loads((E/'NND_CLOSED.json').read_text())['candidates']==[]
assert all(x['match'] for x in json.loads((E/'NND_FROZEN_SOURCE_CHECK.json').read_text()))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
summary={'status':'PASS','extraction_used':len(extract),'formal_scopes_used':len(formal),'kani_used':0,'scope_exits':dict(collections.Counter(str(r['exit_status']) for r in formal)),'current_own_modules':len(modules),'raw_own_roots':len(rows),'raw_axioms':sorted({n for r in rows for n in r['walked_axioms']}),'cache_disagreements':disagreements,'combined_import':{'attempt':'NND_L267','exit_status':0},'target_established':False,'candidate_roots':[],'formal_peak_rss_kib':max(int(r['peak_rss_kib']) for r in formal if r.get('peak_rss_kib') not in [None,'']),'scope_swaps':sorted(set(str(r.get('swaps')) for r in formal)),'cold_release_replay':False,'pushed':False}
(E/'NND_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
