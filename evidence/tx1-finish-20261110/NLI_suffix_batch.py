from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
plan=json.loads((E/'NLI_SUFFIX_PLAN.json').read_text())
start=int(sys.argv[1]);first=sys.argv[2];events=list(plan)
events=events[events.index(first):]
for n,ev in enumerate(events,start):
 assert n<=120
 a=f'NLI_L{n:03d}';m=plan[ev]['module']
 window=E/'NLI_generated'/('NLI_Window_'+ev+'.lean')
 if window.exists():
  # Window targets are compiled explicitly by the split batch below.
  assert any(json.loads(p.read_text()).get('module')=='NLI_Window_'+ev and json.loads(p.read_text())['exit_status']==0 for p in E.glob('NLI_L*/receipt.json')), 'Compile abstract head first: '+ev
 subprocess.run([sys.executable,str(E/'NLI_config.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(E/'NLI_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
