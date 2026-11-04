from pathlib import Path
import subprocess,json,re
E=Path(__file__).resolve().parent;R=E.parent.parent
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();history=[]
for i in range(15):
 r=subprocess.run(['python3',str(E/'NFA_replay_new.py')],cwd=R,capture_output=True,text=True)
 x=json.loads((E/'NFA_NEW_REPLAY.json').read_text());history.append(x)
 print(i,x['exit_status'],x['error'],flush=True)
 if not r.returncode:break
 m=re.fullmatch(r'ModuleNotFoundError\("No module named \'([^\']+)\'"\)',x['error'] or '')
 if not m:break
 name=m[1]+'.py';matches=[p for p in tracked if p.endswith('/'+name)]
 if len(matches)!=1:break
 path=str(Path(matches[0]).parent)
 q=subprocess.run(['git','sparse-checkout','add',path],cwd=R,capture_output=True,text=True)
 assert q.returncode==0,q.stderr
(E/'NFA_NEW_REPLAY_HISTORY.json').write_text(json.dumps(history,indent=2)+'\n')
