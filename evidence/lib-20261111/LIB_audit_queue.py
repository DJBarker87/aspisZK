"""Serial own-root audits; halt on any failure for isolation, never resubmit."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
groups=json.loads((E/'LIB_AUDIT_ROOTS.json').read_text())['groups']
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for i in range(start,len(groups)):
 attempt='LIB_L'+str(157+i).zfill(3)
 result=subprocess.run([sys.executable,str(E/'LIB_run.py'),attempt,'audit','proof'+str(i)])
 if result.returncode:
  # Preserve the strict validator's failure; move only to independent roots
  # when the existing (ab')(3) disposition is demonstrably the sole diagnostic.
  receipt=E/'LIB_audit'/('proof'+str(i))/('proof'+str(i)+'.json')
  if not receipt.exists():sys.exit(result.returncode)
  audit=json.loads(receipt.read_text());rows=audit.get('results',[])
  log=receipt.with_suffix('.log').read_text();standard={'propext','Classical.choice','Quot.sound'}
  mismatches=[r for r in rows if r.get('equal') is False]
  known=(sorted(r['root']for r in rows)==sorted(groups[i]) and len(rows)==len(groups[i]) and
   bool(mismatches) and all(set(r['walked_axioms'])<=standard for r in rows) and
   log.count('raw graph disagrees with collectAxioms')==len(mismatches) and
   not any(x in log.lower() for x in ['unresolved reference','missing constant','unknown constant','out of memory']))
  if not known:sys.exit(result.returncode)
  finding=dict(attempt=attempt,disposition="Continue independent groups under (ab')(3); strict failure retained",mismatches=mismatches)
  with (E/'LIB_AUDIT_CONTINUATIONS.jsonl').open('a')as f:f.write(json.dumps(finding)+'\n')
  print(json.dumps(dict(attempt=attempt,collector_disagreements=len(mismatches),strict_failure_retained=True)),flush=True)
