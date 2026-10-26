from pathlib import Path
import sys,re
P=Path(__file__).resolve().parent;R=P.parents[1]
for i in range(16,25):
 a=(P/'JFm_COMPONENTS'/f'JFm_Q{i:02}Hashes.lean.txt').read_text();b=(P/'JFm_COMPONENTS'/f'JFm_Q{i:02}Source.lean.txt').read_text()
 imports=list(dict.fromkeys(l for text in [a,b] for l in text.splitlines() if l.startswith('import ') and l!=f'import JFm_Q{i:02}Hashes'))
 if i>16:imports=[l.replace(f'JFm_Q{i-1:02}Source',f'JFm_Q{i-1:02}Window') for l in imports]
 body='\n'.join(l for text in [a,b] for l in text.splitlines() if not l.startswith('import '))
 s='\n'.join(imports)+'\n'+body+'\n';f=R/f'lean/JFm_Q{i:02}Window.lean'
 if '--check' in sys.argv:assert f.read_text()==s,str(f)
 else:f.write_text(s)
