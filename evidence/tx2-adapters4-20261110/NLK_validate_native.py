from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent
rows=[]
for line in (E/'NLK_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r.get('kind')!='kani':continue
 a=r['attempt'];p=E/a/'stdout.log.xz';s=lzma.decompress(p.read_bytes()).decode();cfg=json.loads((E/(a+'.json')).read_text());mode=cfg.get('control')
 if 'CBMC timed out' in s or r['exit_status']==124:status='TIMEOUT_NO_CREDIT'
 elif r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s:status='NATIVE_PASS'
 elif mode=='inverse' and (match:=re.search(r'Failed Checks:\s*"([^"\n]+)"',s)) and re.search(r'\*\* 1 of \d+ failed',s) and match[1] in (E/(a+'.patch')).read_text():status='INTENDED_ASSERTION_FAIL'
 elif 'unwinding assertion' in s:status='UNWIND_FAILURE_NO_CREDIT'
 elif 'error[' in s or 'error:' in s:status='COMPILE_OR_GATE_REJECTION_NO_CREDIT'
 else:status='OTHER_FAILURE_NO_CREDIT'
 graph=E/(a+'-graph-check.json');lock=E/(a+'-lock-check.json')
 g=json.loads(graph.read_text()) if graph.exists() else {};l=json.loads(lock.read_text()) if lock.exists() else {}
 assert status not in ['NATIVE_PASS','INTENDED_ASSERTION_FAIL'] or (g.get('graph_matches_frozen') is True and l.get('unchanged') is True),(a,'graph/lock')
 rows.append(dict(attempt=a,module=r['module'],mode=mode,status=status,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],graph_matches_frozen=g.get('graph_matches_frozen'),lock_unchanged=l.get('unchanged'),failed_assertion=match[1] if status=='INTENDED_ASSERTION_FAIL' else None))
assert len(rows)<=60
(E/'NLK_NATIVE_VERDICTS.json').write_text(json.dumps(rows,indent=1)+'\n')
print(json.dumps(dict(attempts=len(rows),statuses={k:sum(x['status']==k for x in rows) for k in sorted(set(x['status'] for x in rows))})))
