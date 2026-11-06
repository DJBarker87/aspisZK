from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
plan=json.loads((E/'NLI_SUFFIX_PLAN.json').read_text())
start=int(sys.argv[1]);first=sys.argv[2];events=list(plan)
events=events[events.index(first):]
for n,ev in enumerate(events,start):
 assert n<=120
 a=f'NLI_L{n:03d}';m=plan[ev]['module']
 subprocess.run([sys.executable,str(E/'NLI_config.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(E/'NLI_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
