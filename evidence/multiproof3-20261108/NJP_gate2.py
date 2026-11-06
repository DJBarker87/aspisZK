from pathlib import Path
import json,lzma,collections,hashlib
E=Path(__file__).resolve().parent
read=lambda p:p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read().decode()
roots=json.loads((E/'NJP_AUDIT_ROOTS.json').read_text())['roots']
metrics=[]
for a in ['NJP_L078','NJP_L079','NJP_L080']:
 r=json.loads((E/a/'receipt.json').read_text());ad=json.loads((E/(a+'-admission.json')).read_text())
 assert r['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 metrics.append({k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
raw=[json.loads(l[11:]) for l in read(E/'NJP_L080/stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
assert sorted(x['root'] for x in raw)==sorted(roots)
assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
scan=[json.loads(l) for l in read(E/'NJP_LOADED_scan.jsonl').splitlines()]
assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
audit=json.loads((E/'NJP_AUDIT.json').read_text());audit.update(combined_audits_used=2,gate2={'combined':'NJP_L078','scan':'NJP_L079','raw':['NJP_L080'],'modules':len(scan),'raw_roots':len(raw),'coherence_defects':0,'standard_axioms_only':True,'metrics':metrics,'fixtures_reused':'L024 eight controls; unchanged driver algorithm/tool pins'},target_established=False)
(E/'NJP_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
(E/'NJP_RAW_RESULTS_GATE2.json').write_text(json.dumps(raw,indent=2)+'\n')
a=[json.loads(l) for l in (E/'NJP_ATTEMPTS.jsonl').read_text().splitlines()]
count=collections.Counter(x['kind'] for x in a)
assert count['kani']==70 and sum(count[k] for k in ['lean','link','audit'])==80
for x in a:
 assert x['exit_status'] is not None
 cfg=json.loads((E/(x['attempt']+'.json')).read_text())
 assert cfg['env'].get('CARGO_TARGET_DIR','').endswith('/NJP_target'),x['attempt']
receipt_metrics=[]
for x in a:
 r=json.loads((E/x['attempt']/'receipt.json').read_text())
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 receipt_metrics.append({k:r.get(k) for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','limits']})
summary={'counts':dict(count),'kani_used':70,'kani_budget':70,'lean_link_audit_used':80,'lean_budget':80,'extraction_used':0,'metrics':receipt_metrics,'target_established':False}
(E/'NJP_RESOURCE_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
for name in ['NJP_CLOSED.json','NJP_ROW_PACKETS.json']:
 obj=json.loads((E/name).read_text())
 if isinstance(obj,dict):obj['final_own_gate']='L078/L079/L080 PASS, two combined audits used; lead ledger credit pending'
 else:
  for row in obj:row['admission']='Both own combined gates PASS; local candidate, next lead ledger gate required'
 (E/name).write_text(json.dumps(obj,indent=2)+'\n')
print(f'Final gate PASS: {len(scan)} coherent modules, {len(raw)} standard-only raw roots; budgets 70/70 and 80/80')
