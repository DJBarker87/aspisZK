from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
plan=json.loads((E/'NLI_SUFFIX_PLAN.json').read_text())
events=list(plan);events=events[events.index(sys.argv[2]):]
n=int(sys.argv[1])
for ev in events:
 modules=[]
 w=E/'NLI_generated'/('NLI_Window_'+ev+'.lean')
 if w.exists():modules.append('NLI_Window_'+ev)
 modules.append(plan[ev]['module'])
 for m in modules:
  a=f'NLI_L{n:03d}';assert n<=120
  subprocess.run([sys.executable,str(E/'NLI_config.py'),a,m],check=True)
  r=subprocess.run([sys.executable,str(E/'NLI_run.py'),a])
  if r.returncode:sys.exit(r.returncode)
  n+=1
