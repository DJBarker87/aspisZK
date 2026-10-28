"""One focused source module per attempt; stop on first error/refusal for review."""
from pathlib import Path
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028'
rows=json.loads((E/'source-frontier.json').read_text());receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')];accepted={r['target'].replace('/','.') for r in receipts if r.get('accepted')};a=int(sys.argv[1])
skip=json.loads((E/'source-skip.json').read_text()) if (E/'source-skip.json').exists() else {}
# First complete the dependency frontier of the actual emitted native caller.
by={r['module']:r for r in rows};priority=set()
def visit(m):
 if m in priority:return
 priority.add(m)
 for d in by[m]['dependencies']:visit(d)
visit('PV_L1_Source_072')
rows=[r for r in rows if r['module'] in priority]+[r for r in rows if r['module'] not in priority]
for row in rows:
 m=row['module']
 if m in accepted or m in skip:continue
 if a>=51697:print('Focused attempt block exhausted; three audit IDs retained',flush=True);break
 assert not (E/f'receipt-{a}.json').exists()
 print('FOCUSED',a,m,row['source_function'],flush=True)
 r=subprocess.run([sys.executable,str(R/'tools/pv-l1-20261028/check.py'),str(a),m],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(r.stdout[-4500:] if r.returncode else r.stdout[-800:],flush=True)
 if r.returncode:print('REVIEW',a,m,'exit',r.returncode,flush=True);sys.exit(r.returncode)
 a+=1
 if m=='PV_L1_Source_072' and '--priority-only' in sys.argv:break
