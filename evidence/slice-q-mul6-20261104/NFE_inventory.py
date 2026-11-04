from pathlib import Path
import subprocess,lzma,json,re,hashlib
E=Path(__file__).resolve().parent
files=subprocess.check_output(['git','ls-files'],text=True).splitlines()
cohort={r['module']:r for r in map(json.loads,lzma.open('evidence/coherent-20261102/NER_STREAM_B_COHORT.jsonl.xz','rt'))}
idx={}
for p in files:
 if p.endswith('.lean'): idx.setdefault(Path(p).stem,[]).append(p)
used={};boundary={};missing=[]
def source(m):
 paths=idx.get(m,[]) if '.' not in m else [p for p in files if p.endswith('/'+m.replace('.', '/')+'.lean')]
 paths=sorted(paths,key=lambda p:(not p.startswith('evidence/slice-q-mul5-20261104/'),not p.startswith('evidence/slice-q-mul4-20261104/'),not p.startswith('lean/'),len(p),p))
 if not paths:return None,None
 p=paths[0];return p,subprocess.check_output(['git','show','HEAD:'+p],text=True)
def visit(m):
 if m in used or m in boundary:return
 if m in cohort:boundary[m]=cohort[m];return
 p,s=source(m)
 if s is None:missing.append(m);return
 imports=[n for l in s.splitlines() if l.startswith('import ') for n in l[7:].split() if n!='all']
 used[m]=dict(path=p,sha256=hashlib.sha256(s.encode()).hexdigest(),imports=imports)
 for n in imports:visit(n)
visit('NFC_FinalAudit')
retarget={m:'RPt_'+m for m in used if 'RPt_'+m in cohort}
(E/'NFE_INVENTORY.json').write_text(json.dumps(dict(used=used,boundary=list(boundary),retarget=retarget,missing=sorted(set(missing))),indent=2)+'\n')
print('modules',len(used),'boundary',len(boundary),'retarget',retarget,'missing',sorted(set(missing)))
