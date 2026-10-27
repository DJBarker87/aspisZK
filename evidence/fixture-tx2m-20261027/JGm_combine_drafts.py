from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
for group in ['Initial','Valid','Levels','Verify','Terminal']:
 sources=[]
 for t in range(3):
  q=P/'JGm_STAGE_PARTS'/f'JGm_TX2_{group}{t}.lean.txt'
  sources.append(q.read_text())
 imports=sorted(set(line for s in sources for line in s.splitlines() if line.startswith('import ')))
 replacements={f'JGm_TX2_{x}{t}':f'JGm_TX2_{x}' for x in ['Initial','Valid','Levels','Verify'] for t in range(3)}
 imports=sorted(set('import '+replacements.get(line[7:],line[7:]) for line in imports))
 bodies=['\n'.join(line for line in s.splitlines() if not line.startswith('import ')) for s in sources]
 s='\n'.join(imports)+'\n'+'\n'.join(bodies)+'\n'
 q=R/f'lean/JGm_TX2_{group}.lean'
 if '--check' in sys.argv:assert q.read_text()==s,q
 else:q.write_text(s)
 print(group,'combined into one focused stage module')
