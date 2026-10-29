from pathlib import Path
import sys,subprocess,re,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029')
module,start,end,*offset=sys.argv[1:];start=int(start);end=int(end);offset=int(offset[0]) if offset else 0
full=(D/(module+'.lean')).read_text(); chunks=full.removesuffix('end PV_DIAG8\n').split('-- NEXT\n')
assert end-start+1+offset <= len(chunks)
for i in range(end-start+1):
 text=''.join(chunks[:i+1+offset])+'end PV_DIAG8\n'
 (D/'sources'/(module+'.lean')).write_text(text)
 p=subprocess.run(['python3',str(D/'run.py'),'lean'+str(start+i),'lean',str(start+i),module])
 if p.returncode:sys.exit(p.returncode)
