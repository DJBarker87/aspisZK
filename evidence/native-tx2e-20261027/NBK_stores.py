from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[]
for n in [688,800]:
 for k in range(20):
  if n==688 and k==0:continue
  jobs.append((f'NBK_K{len(jobs)+2:03}',f'pool_v1::pair_terminal::NBK_codecs::NBK_store{n}_{k:02}'))
(E/'NBK_STORE_JOBS.json').write_text(json.dumps(jobs,indent=2)+'\n')
for a,h in jobs:
 if (E/a/'receipt.json').exists():
  rc=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph.json')).read_text())
  assert rc['exit_status']==0 and g['lock_unchanged'] and g['graph_matches_frozen'],a
  continue
 r=subprocess.run(['python3',str(E/'NBK_native.py'),'run',a,h])
 if r.returncode:sys.exit(r.returncode)
