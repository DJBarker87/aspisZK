"""One partitioned raw audit, never re-run a receipt-bearing target."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;plan=json.loads((E/'NLZ_AUDIT_PLAN.json').read_text());manifest=json.loads((E/'NLZ_AUDIT_ROOTS.json').read_text())
for j in range(plan['groups']):
 a=f"NLZ_L{plan['raw_start']+j:03}";receipt=E/a/'receipt.json'
 if receipt.exists():continue
 r=subprocess.run([sys.executable,str(E/'NLZ_run.py'),a])
 p=E/'NLZ_audit'/('proof'+str(j))/('proof'+str(j)+'.json')
 if not p.exists():raise SystemExit('Recover missing audit packaging read-only: '+a)
 x=json.loads(p.read_text());roots=[v['root']for v in x['results']]
 if sorted(roots)!=sorted(manifest['groups'][j]):raise SystemExit('Incomplete raw root group: '+a)
 if any(not set(v['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for v in x['results']):raise SystemExit('Nonstandard raw axiom: '+a)
 if r.returncode and not(r.returncode==1 and any(not v['equal']for v in x['results'])):raise SystemExit('Unexpected raw audit failure: '+a)
 print(json.dumps(dict(group=j,groups=plan['groups'],roots=len(roots),exit=r.returncode,standard_only=True)),flush=True)
