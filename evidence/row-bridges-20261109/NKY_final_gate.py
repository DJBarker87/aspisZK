from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
steps=[('NKY_L036','lean','NKY_COMBINED_IMPORT'),('NKY_L037','audit','scan')]
steps += [(f'NKY_L{38+i:03}','audit','batch'+str(i)) for i in range(len(json.loads((E/'NKY_AUDIT_ROOTS.json').read_text())['groups']))]
steps += [('NKY_L068','audit','close')]
for a,k,t in steps:
 r=subprocess.run([sys.executable,str(E/'NKY_run.py'),a,k,t])
 if r.returncode:
  if t.startswith('batch'):
   # Preserve all raw audit outcomes; classification is explicit, never rerun.
   print(a,'nonzero raw group retained for exact classification',flush=True)
   continue
  raise SystemExit(r.returncode)
 print(a,t,'complete',flush=True)
