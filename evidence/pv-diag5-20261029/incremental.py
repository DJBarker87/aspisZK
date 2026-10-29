"""Compile one newly added law at a time; never replay an unchanged source.
Stop on any compiler error, admission refusal, or budget limit.
"""
from pathlib import Path
import subprocess,sys,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029')
module,start=sys.argv[1],int(sys.argv[2]);raw=(D/(module+'.lean')).read_text();parts=raw.split('-- STAGE\n');end='end PV_DIAG5\n';assert parts[-1].endswith(end);parts[-1]=parts[-1][:-len(end)]
skip=int(sys.argv[3]) if len(sys.argv)>3 else 1
for j in range(skip,len(parts)):
 n=start+j-skip;assert n<65097
 s=D/'sources'/(module+'.lean');s.write_text(''.join(parts[:j+1])+end)
 p=subprocess.run(['python3',str(D/'run.py'),'lean'+str(n),'lean',str(n),module])
 if p.returncode:sys.exit(p.returncode)
print('FINISHED',module,'next',start+len(parts)-skip)
