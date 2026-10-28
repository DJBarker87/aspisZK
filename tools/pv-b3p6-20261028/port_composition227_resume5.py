"""Reuse every identical compiled body; port only the factored composition.
The fresh raw extraction stays immutable. The final root's import is redirected
through the new helper and composition, preserving the root definition itself.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'raw227-composition-resume5';O=D/'raw227-parts-resume5'
blocks=lambda s:re.split(r'(?=^/-- \[)',s,flags=re.M)
def name(b):
 m=re.search(r'^(?:def|structure|inductive)\s+(\S+)',b,re.M);return m[1]if m else None
def body(b):
 m=re.search(r'^(?:def|structure|inductive)\s+',b,re.M);assert m
 return re.sub(r'\s+',' ',re.sub(r'\nend PV_B3P_227\s*$','',b[m.start():])).strip()
for kind in ('Types','Funs'):
 old={name(b):b for b in blocks((O/(kind+'.lean')).read_text())if name(b)};new={name(b):b for b in blocks((R/(kind+'.lean')).read_text())if name(b)}
 if kind=='Types':assert old.keys()==new.keys();assert all(body(old[n])==body(new[n])for n in old);continue
 changed=[n for n in old if body(old[n])!=body(new[n])];added=[n for n in new if n not in old];assert changed==['reference_terminal.composition_parts'],changed;assert added==['reference_terminal.select_c1_227'],added
 header=blocks((R/'Funs.lean').read_text())[0].replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n');header=re.sub(r'^import \S+\.Types$','import PV_B3P_P227_13a\nimport PV_B3P_Length227',header,flags=re.M)
 code=header+new[added[0]]+new[changed[0]];code=re.sub(r'\nend PV_B3P_227\s*$','',code)
 # New fixed16 array has sixteen named values; use its symbolic size theorem.
 edits=[]
 for m in re.finditer(r'Array\.make (\d+)#usize \[',code):
  n=int(m[1]);i=m.end();start=i;depth=1;xs=[]
  while depth:
   c=code[i]
   if c in '[({':depth+=1
   if c in '])}':depth-=1
   if c==',' and depth==1:xs.append(code[start:i].strip());start=i+1
   i+=1
  xs.append(code[start:i-1].strip());assert len(xs)==n and n==16
  edits.append((i,' (PV_B3P_Length227.size16 '+ ' '.join('('+x+')'for x in xs)+')'))
 for i,text in sorted(edits,reverse=True):code=code[:i]+text+code[i:]
 code+='\nend PV_B3P_227\n\n'+''.join('#print axioms PV_B3P_227.'+n+'\n'for n in added+changed)
 q=D/'lean/PV_B3P_P227_13b.lean';q.write_text(code)
 p=D/'lean/PV_B3P_P227_14.lean';before=p.read_text();after=before.replace('import PV_B3P_P227_13\n','import PV_B3P_P227_13b\n');assert before==after or before.count('import PV_B3P_P227_13\n')==1;p.write_text(after)
 (D/'port-composition227-resume5.json').write_text(json.dumps(dict(raw_funs_sha256=hashlib.sha256((R/'Funs.lean').read_bytes()).hexdigest(),types_all_identical=True,changed=changed,added=added,all_other_bodies_identical=True,module_sha256=hashlib.sha256(code.encode()).hexdigest(),named_literal_proofs=len(edits),root_body_unchanged=True,root_import='PV_B3P_P227_13b',root_sha256=hashlib.sha256(after.encode()).hexdigest(),numeric_ports=[],raw_modified=False),indent=2)+'\n')
 print('new helper and composition ported; all other bodies identical')
