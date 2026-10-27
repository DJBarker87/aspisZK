"""Compact existing certificate assembly; preserve literal data and theorem types."""
from pathlib import Path
import re,sys,hashlib,json
R=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent

def compact(f):
 s=f.read_text().replace('import JFp_SHABlocks','import JGy_FoldStep',1)
 s=s.replace('AspisR1.JGr_', 'AspisR1.JGy_Gr_')
 pattern=r'theorem checked : compress start \(words input\)=result := by\n.*?(?=#print axioms checked)'
 def sub(m):
  lines=['theorem checked : compress start (words input)=result := by', '  have run : (constants.foldl transition (w00,s00)).2=s64 := by']
  for i in range(64):lines.append(f'    apply JGy_FoldStep.step _ _ w{i:02} w{i+1:02} s{i:02} s{i+1:02} s64 word{i:02} round{i:02}')
  lines+=['    rfl','  exact JGy_FoldStep.compression input w00 start s64 result parsed run (by rfl)']
  return '\n'.join(lines)+'\n'
 s,n=re.subn(pattern,sub,s,flags=re.S);assert n>0
 return s,n

sources={};plan=[]
for f in sorted((R/'lean').glob('JGr_M*C*.lean')):
 s,n=compact(f);sources[f.stem]=s
 plan.append(dict(original=f.stem,source_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),blocks=n))
# First affected module is checked independently before further generation.
new,_=compact(R/'lean/JGr_M0C000.lean')
f=R/'lean/JGy_CompactFirst.lean'
if '--check' in sys.argv:
 assert f.read_text()==new
else:f.write_text(new)
(P/'JGy_COMPACT_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
print('Checked compression plan:',len(plan),'modules;',sum(x['blocks'] for x in plan),'blocks')
if '--groups' in sys.argv:
 manifest=[]
 for tree in range(3):
  fs=sorted((R/'lean').glob(f'JGr_M{tree}C*.lean'))
  for g in range(0,len(fs),2):
   mod=f'JGy_Certs{tree}_{g//2:02}'
   texts=[]
   for f in fs[g:g+2]:
    text,_=compact(f)
    text=re.sub(r'theorem (word|round)\d\d[^\n]*\n','',text)
    text=re.sub(r'#print axioms (word|round)\d\d\n','',text)
    text=re.sub(r' s64 word\d\d round\d\d',r' s64 (by rfl) (by rfl)',text)
    texts.append('\n'.join(l for l in text.splitlines() if not l.startswith('import '))+'\n')
   imports=['JGy_FoldStep']
   mapping={f.stem:f'JGy_Certs{tree}_{j//2:02}' for j,f in enumerate(fs)}
   for original in fs[g:g+2]:
    for dependency in re.findall(r'^import (\w+)',original.read_text(),re.M):
     dependency=mapping.get(dependency,dependency)
     if dependency not in [mod,'JFp_SHABlocks'] and dependency not in imports:imports.append(dependency)
   text=''.join('import '+x+'\n' for x in imports)+'\n'.join(texts)
   f=R/'lean'/f'{mod}.lean'
   if '--check' in sys.argv:assert f.read_text()==text
   else:f.write_text(text)
   manifest.append(dict(module=mod,originals=[f.stem for f in fs[g:g+2]],source_sha256=hashlib.sha256(text.encode()).hexdigest(),blocks=sum(compact(f)[1] for f in fs[g:g+2])))
 (P/'JGy_GROUPS.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print('Groups',len(manifest))
