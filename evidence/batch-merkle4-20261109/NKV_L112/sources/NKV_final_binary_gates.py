"""Sequential fresh fixtures, NFX loaded scan, raw ax2; same pinned binaries.
No compiler invocation, no timeout/cap increase, and no shared infrastructure edit.
"""
from pathlib import Path
import json,subprocess,time,re,hashlib,os,sys
P=Path.cwd();cfg=json.loads((P/sys.argv[1]).read_text());metrics=[]
for mode in ['scan','raw']:
 label='NKV_FINAL_'+mode
 cmd=['python3','NKV_audit_binary.py',mode]
 start=time.monotonic()
 r=subprocess.run(['/usr/bin/time','-v','-o',label+'.time']+cmd,text=True,capture_output=True)
 (P/(label+'.stdout.log')).write_text(r.stdout);(P/(label+'.stderr.log')).write_text(r.stderr)
 timing=(P/(label+'.time')).read_text()
 def stat(name):
  h=re.search(r'^\s*'+re.escape(name)+r':\s*(.+)$',timing,re.M);assert h,name;return h[1]
 record=dict(target=mode,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,
   peak_rss_kib=int(stat('Maximum resident set size (kbytes)')),swaps=int(stat('Swaps')),
   source_revision=cfg['source_revision'],cargo_target_dir=os.environ['CARGO_TARGET_DIR'],
   roots_sha256=hashlib.sha256((P/'NKV_AUDIT_ROOTS.json').read_bytes()).hexdigest())
 metrics.append(record);(P/'NKV_FINAL_METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
 print(json.dumps(record),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if mode=='scan':
  rows=[json.loads(line) for line in (P/'NKV_LOADED_scan.jsonl').read_text().splitlines()]
  assert rows
  assert all(not row['dangling'] and not row['duplicate_owners'] and row['imports_match'] for row in rows)
  (P/'NKV_NFX_RESULT.json').write_text(json.dumps(dict(exit_status=0,modules=len(rows),
    declarations=sum(row['declarations'] for row in rows),edges=sum(row['edges'] for row in rows),
    dangling=0,duplicate_owners=0,imports_mismatch=0),indent=2)+'\n')
 else:
  results=[json.loads(line.removeprefix('NEP_RESULT ')) for line in r.stdout.splitlines() if line.startswith('NEP_RESULT ')]
  expected=set(json.loads((P/'NKV_AUDIT_ROOTS.json').read_text())['roots']);assert {x['root'] for x in results}==expected
  assert len(results)==len(expected)
  std={'propext','Classical.choice','Quot.sound'}
  assert all(x['equal'] and set(x['walked_axioms'])<=std and set(x['collect_axioms'])<=std for x in results)
  (P/'NKV_AX2_RESULT.json').write_text(json.dumps(dict(exit_status=0,roots=len(results),
    roots_sha256=record['roots_sha256'],all_equal=True,all_standard_axioms=True,results=results),indent=2)+'\n')
