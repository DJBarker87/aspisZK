from pathlib import Path
import subprocess,hashlib,json,re,difflib
E=Path(__file__).resolve().parent.parent
raw=E/'extraction/control21';raw.mkdir(parents=True,exist_ok=True)
dst=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1SimControl21');dst.mkdir(exist_ok=True)
manifest=[]
for name in ['Types.lean','Funs.lean']:
 subprocess.run(['scp','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021/extraction/generated-sim-tail-control-v2/AspisR1SimControl21/'+name,str(raw/(name+'.txt'))],check=True)
 original=(raw/(name+'.txt')).read_text()
 text=original.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n')
 if name=='Types.lean':
  text=text.replace('@[discriminant isize]\n','')
  # Declaration-order expansion used in the already accepted part-20 port.
  additions=[]
  for enum in ['verifier.Error','transport.Variant']:
   body=re.search(r'inductive '+re.escape(enum)+r' where\n((?:\|[^\n]*\n)+)',text)[1]
   constructors=re.findall(r'^\| (\w+) :',body,re.M)
   additions += ['def '+enum+'.read_discriminant : '+enum+' → Isize']+['  | .'+n+' => '+str(i)+'#isize' for i,n in enumerate(constructors)]
   additions += ['instance : Discriminant '+enum+' Isize where','  read_discriminant := '+enum+'.read_discriminant','']
  text=text.replace('end AspisR1SimControl21','\n'.join(additions)+'\nend AspisR1SimControl21')
 (dst/name).write_text(text)
 (raw/(name+'.diff')).write_text(''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='raw/'+name,tofile='promoted/'+name)))
 manifest.append(dict(file=name,raw_sha256=hashlib.sha256(original.encode()).hexdigest(),promoted_sha256=hashlib.sha256(text.encode()).hexdigest()))
(raw/'promotion.json').write_text(json.dumps(dict(files=manifest,edits=['Narrow root Aeneas import to pinned cached Std/RustAttributes/Discriminant','Expand enum discriminants by declaration order; unchanged constructors'],scope='Explicit generic sampler policy callbacks; no source sampler equation is assumed'),indent=2)+'\n')
