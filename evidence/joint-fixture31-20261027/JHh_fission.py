"""Proof-source fission only; no launcher or host infrastructure."""
from pathlib import Path
import re,sys,json,hashlib
P=Path(__file__).resolve().parent;L=P.parents[1]/'lean';check='--check' in sys.argv
manifest=[]
for t in range(3):
 source=P/'JHh_SPLIT_INPUTS'/f'JHh_C_Tree{t}B.lean.txt';s=source.read_text()
 xs=[m.start() for m in re.finditer(r'(?m)^set_option autoImplicit false$',s)]
 assert len(xs)==19,(t,len(xs))
 header=s[:xs[0]];chunks=[s[a:b] for a,b in zip(xs,xs[1:]+[len(s)])]
 assert chunks[-1].endswith('end\n');chunks[-1]=chunks[-1][:-4]
 previous=None;outputs={}
 for a,b,tag in [(0,1,'P'),(1,6,'L0'),(6,13,'L1'),(13,16,'V0'),(16,19,'V1')]:
  name=f'JHh_C_Tree{t}B' if t>0 and tag=='V1' else f'JHh_C_Tree{t}B_{tag}'
  text=('import '+previous+'\n' if previous else '')+header+''.join(chunks[a:b])+'\nend\n'
  if tag=='P' and t>0:
   numeric=(P/'JHh_SPLIT_INPUTS'/f'JHh_LeafNumerics{t}.lean.txt').read_text()
   numeric='\n'.join(line for line in numeric.splitlines() if not line.startswith('import '))
   text=text.replace('section\nvariable',numeric+'\nsection\nvariable',1)
  if tag in ['L0','L1']:
   if t==0:text='import JHh_LeafNumerics0\n'+text
   owner='JHe_C_Gr_M0Roots' if t==0 else f'JHh_C_Gr_M{t}Roots'
   text=text.replace(owner+'.numeric',f'JHh_LeafNumerics{t}.numeric')
  outputs[name]=text;previous=name
 if t==0:outputs[f'JHh_C_Tree{t}B']='import '+previous+'\n'
 for name,text in outputs.items():
  path=L/(name+'.lean')
  if check:assert path.read_text()==text,name
  elif not path.exists() or path.read_text()!=text:path.write_text(text)
 manifest.append(dict(tree=t,input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),outputs={n:hashlib.sha256(v.encode()).hexdigest() for n,v in outputs.items()}))
(P/'JHh_FISSION.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(check=check,trees=3,files=sum(len(r['outputs']) for r in manifest))))
