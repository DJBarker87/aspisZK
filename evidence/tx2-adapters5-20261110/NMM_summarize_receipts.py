from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
attempts=[json.loads(l) for l in (E/'NMM_ATTEMPTS.jsonl').read_text().splitlines()]
rows=[]
for x in attempts:
 if x.get('kind')!='kani':continue
 a=x['attempt'];p=E/a/'stdout.log.xz';s=lzma.decompress(p.read_bytes()).decode() if p.is_file() else '';control=x.get('control','unknown')
 if not p.is_file():status='UNRESOLVED_CHARGED_NO_CREDIT'
 elif 'timed out' in s.lower() or x.get('exit_status')==124:status='TIMEOUT_RETIRED_NO_CREDIT'
 elif 'could not compile' in s or 'error[E' in s:status='COMPILER_REJECT_NO_CREDIT'
 elif x.get('exit_status')==0 and 'VERIFICATION:- SUCCESSFUL' in s:status='LOCAL_NATIVE_PASS' if control=='positive' else 'NEGATIVE_CONTROL_DID_NOT_FAIL'
 elif x.get('exit_status')==1 and 'VERIFICATION:- FAILED' in s:status='EXPECTED_NEGATIVE_FAILURE' if control!='positive' else 'NATIVE_PROPERTY_FAILURE'
 else:status='UNCLASSIFIED_NO_CREDIT'
 rows.append(dict(attempt=a,module=x.get('module'),control=control,status=status,exit_status=x.get('exit_status'),wall_seconds=x.get('wall_seconds'),peak_rss_kib=x.get('peak_rss_kib'),swaps=x.get('swaps'),source_revision=x.get('source_revision'),source_hashes=x.get('source_hashes',{})))
assert len({x['attempt'] for x in rows})==len(rows)
formal=[x for x in attempts if x.get('kind') in ['lean','audit','link','cache'] and x.get('attempt','').startswith('NMM_L')]
summary=dict(kani_charged=len(rows),kani_limit=80,formal_scopes=len(formal),formal_limit=60,extractions=0,native=rows,counts={s:sum(x['status']==s for x in rows) for s in sorted({x['status'] for x in rows})},wait_records=sum(x.get('kind')=='wait' for x in attempts),security_target_established=False,candidate_rows=[],promotions=[])
(E/'NMM_ATTEMPT_SUMMARY.json').write_text(json.dumps(summary,indent=1)+'\n')
retired=[x for x in rows if x['status']=='TIMEOUT_RETIRED_NO_CREDIT']
(E/'NMM_RETIRED_SHAPES.json').write_text(json.dumps(dict(policy='No unchanged timeout/memory-kill rerun; original snapshots remain in NMM_INPUTS.json.',attempts=retired),indent=1)+'\n')
print(json.dumps({k:summary[k] for k in ['kani_charged','formal_scopes','extractions','counts','wait_records']}))
