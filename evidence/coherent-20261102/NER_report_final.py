"""Publish reports only from successful, complete saved final evidence."""
import hashlib,json,lzma,shutil
from pathlib import Path
E=Path(__file__).resolve().parent
receipt=json.loads((E/'NER_A901/receipt.json').read_text());assert receipt['exit_status']==0
log=(E/'NER_A901/stdout.log').read_text()
assert 'NER_SCAN_ZERO_DANGLING' in log and 'NER_POSTAGG_INPUTS_UNCHANGED' in log
results=[json.loads(line.split('NEP_RESULT ',1)[1]) for line in log.splitlines() if line.startswith('NEP_RESULT ')]
assert len(results)==2 and all(r['equal'] and r['walked_axioms']==r['collect_axioms']==['Classical.choice','Quot.sound','propext'] for r in results)
def lines(name):
 p=E/name
 if p.exists():return [json.loads(l) for l in p.read_text().splitlines()]
 b=lzma.decompress((E/(name+'.xz')).read_bytes());assert hashlib.sha256(b).hexdigest()==(E/(name+'.sha256')).read_text().strip()
 return [json.loads(l) for l in b.splitlines()]
rows=lines('NER_LOADED_final.jsonl');assert len(rows)==16058
assert all(r['imports_match'] and not r['dangling'] for r in rows)
for old,new in [('NER_SCAN.json','NER_SCAN_PRE_REBUILD.json'),('NER_AXIOMS.json','NER_AXIOMS_FOCUSED.json')]:
 if not (E/new).exists():shutil.copyfile(E/old,E/new)
scan=dict(status='coherent',method='Private active-kernel declarations; types, values, recursor rules, metadata; stable first-occurrence import projection identical to original cohort index',module_count=len(rows),declarations=sum(r['declarations'] for r in rows),edges=sum(r['edges'] for r in rows),imports_all_match=True,dangling_modules=[],receipt='NER_A901/receipt.json',rows='NER_LOADED_final.jsonl.xz',historical_scan='NER_SCAN_PRE_REBUILD.json',rebuild_order=json.loads((E/'NER_SCAN_PRE_REBUILD.json').read_text())['rebuild_order'])
(E/'NER_SCAN.json').write_text(json.dumps(scan,indent=2)+'\n')
focused=json.loads((E/'NER_AXIOMS_FOCUSED.json').read_text())['focused']
ax=dict(status='complete_coherent_roots',final_agg16_runs=2,roots=[{**r,'raw_complete':True,'status':'complete','receipt':'NER_A901/receipt.json','print_axioms':[s for s in receipt['print_axioms'] if r['root'] in s]} for r in results],focused=focused,source_revision=receipt['source_revision'],command=receipt['command'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],limits=receipt['limits'],cohort_manifest='NER_STREAM_B_COHORT.jsonl.xz')
(E/'NER_AXIOMS.json').write_text(json.dumps(ax,indent=2)+'\n')
batches=[]
for p in sorted(E.glob('NER_B*/receipt.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0
 batches.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','limits','cgroup_memory_peak_bytes']})
(E/'NER_BATCH_SUMMARY.json').write_text(json.dumps(batches,indent=2)+'\n')
meta=dict(modules=16058,rebuilt=1387,cohort_sha256=(E/'NER_STREAM_B_COHORT.jsonl.sha256').read_text().strip(),aggregate_receipt='NER_A901/receipt.json',aggregate_compilation_receipt='NER_A900/receipt.json',corrected_failure='NER_A900_DIAGNOSIS.json',lean_binary_sha256='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',audit_helper_sha256='41972f6b2ca5eadbe2caa799e1416234f9690a9aa5560351a69926baf4390c92',lean_path=receipt['env']['LEAN_PATH'],source_revision=receipt['source_revision'],scope_usage=dict(batch_scopes=len(batches),new_scanner_and_driver_controls=4,continuation_capped_total=len(batches)+4,continuation_capped_budget=120,agg16_runs=2,agg16_budget=2),source_provenance='All 1387 rebuilt objects have exact source/import pins. Unchanged upstream objects retain original cohort hashes; source_basis distinguishes original successful receipt matches from source-file inventory.',inputs_verified_before_and_after=True)
(E/'NER_STREAM_B_COHORT_META.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(status='complete',batch_scopes=len(batches),modules=scan['module_count'],declarations=scan['declarations'],edges=scan['edges'],roots=results)))
