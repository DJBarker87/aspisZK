#!/usr/bin/env python3
"""Repair source cache in dependency order; never automatically rerun a failed compile."""
import pathlib,json,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
order=json.loads((e/'resume6-projection-rebuild-order.json').read_text()); limit=int(sys.argv[1]) if len(sys.argv)>1 else 97
for m in order:
 prior=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()] if (e/'resume6-attempts.jsonl').exists() else []
 if len(prior)>=limit:break
 if any(r['module']==m.replace('.','/') and r['exit']==0 for r in prior):continue
 # Existing failed declarations require inspection and a changed proof/source, not a retry.
 if any(r['module']==m.replace('.','/') and r['exit']!=0 for r in prior):print('FAILED TARGET NEEDS REVIEW',m);sys.exit(1)
 if m in {'R1Z.EventsR1P2','R1Z.SimCostOuterRetry6'}:print('DEDICATED OWNER TARGET',m);sys.exit(1)
 r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume6-run-one.py'),m])
 if r.returncode:sys.exit(r.returncode)
