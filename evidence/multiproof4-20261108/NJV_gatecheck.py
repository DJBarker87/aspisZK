from pathlib import Path
import json,lzma,hashlib,sys,collections
E=Path(__file__).resolve().parent;gate=int(sys.argv[1]);ids=[65,66,67] if gate==1 else [68,69,70]
read=lambda p:p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read().decode()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
metrics=[]
for n in ids:
 a=f'NJV_L{n:03d}';r=json.loads((E/a/'receipt.json').read_text());ad=json.loads((E/(a+'-admission.json')).read_text())
 assert r['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 metrics.append({k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
roots=json.loads((E/'NJV_AUDIT_ROOTS.json').read_text())['roots']
raw=[json.loads(l[11:]) for l in read(E/f'NJV_L{ids[2]:03d}'/'stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
assert sorted(x['root'] for x in raw)==sorted(roots)
assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
scantext=read(E/'NJV_LOADED_scan.jsonl');scan=[json.loads(l) for l in scantext.splitlines()]
assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
result=dict(gate=gate,combined=metrics[0]['attempt'],scan=metrics[1]['attempt'],raw=metrics[2]['attempt'],metrics=metrics,loaded_modules=len(scan),declarations=sum(x['declarations'] for x in scan),references=sum(x['edges'] for x in scan),cached_replicas=sum(len(x.get('cached_replicas',[])) for x in scan),coherence_defects=0,scan_sha256=sha(scantext),roots=len(raw),standard_axioms_only=True,raw_equals_collectAxioms=True,headline='AspisR1.RPx_Deployed.deployed',target_established=False)
(E/f'NJV_GATE{gate}.json').write_text(json.dumps(result,indent=2)+'\n');(E/f'NJV_RAW_RESULTS_GATE{gate}.json').write_text(json.dumps(raw,indent=2)+'\n')
(E/f'NJV_GATE{gate}_LOADED_scan.jsonl.xz').write_bytes(lzma.compress(scantext.encode(),preset=6));(E/f'NJV_GATE{gate}_LOADED_scan.jsonl.sha256').write_text(sha(scantext)+'\n')
audit=json.loads((E/'NJV_AUDIT.json').read_text()) if (E/'NJV_AUDIT.json').exists() else dict(gates=[],combined_audits_limit=2)
audit['gates']=[x for x in audit['gates'] if x['gate']!=gate]+[result];audit.update(combined_audits_used=gate,final_gate=gate,fixtures='NJV_L064: eight unchanged raw walker/metadata fidelity fixtures in the SAME optimized proof binary',target_established=False,standard_axioms_only=True)
(E/'NJV_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
print(f'NJV gate{gate} PASS: {len(scan)} modules, {len(raw)} raw-standard roots, zero defects, swap0')
