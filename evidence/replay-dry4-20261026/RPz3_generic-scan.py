"""Find generic committed source snapshots by exact retained import signature."""
from pathlib import Path
import json,re,subprocess,hashlib,collections,ast
E=Path(__file__).resolve().parent;R=E.parents[1];p=json.loads((E/'RPz3_source-plan.json').read_text());old=json.loads((R/'evidence/replay-dry3-20261026/RPz2_inherited-source-manifest.json').read_text())['modules'];tree=ast.parse((E/'RPz3_closure.py').read_text());node=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='strip');d={};exec(compile(ast.Module(body=[node],type_ignores=[]),'strip','exec'),d);strip=d['strip']
want=collections.defaultdict(list)
for m in p['unresolved']:
 im=old.get(m,{}).get('imports')
 if im:want[tuple(sorted(set(im)))].append(m)
found=collections.defaultdict(list);hashhits=[];fs=subprocess.check_output(['git','ls-files','*.lean','*.lean.txt'],text=True).splitlines()
for f in fs:
 data=(R/f).read_bytes();sha=hashlib.sha256(data).hexdigest()
 if sha=='674a9e12da22944712ab23b127ec52834b179af3cf7c97f7759e49d2e0574585':hashhits.append(f)
 s=strip(data.decode());im=[] if re.search(r'^\s*prelude\b',s,re.M) else ['Init']
 for l in s.splitlines():
  z=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',l)
  if z:im += [n for n in re.findall(r'[A-Za-z_][\w.]*',z[1]) if n!='all']
 key=tuple(sorted(set(im)))
 for m in want.get(key,[]):found[m].append({'path':f,'sha256':sha,'bytes':len(data),'namespace_lines':re.findall(r'^namespace (.*)$',s,re.M)})
(E/'RPz3_generic-scan.json').write_text(json.dumps({'files_scanned':len(fs),'matches':dict(found),'R1FirstFold_exact_source_hash_hits':hashhits,'qualification':'Import-signature matches are source-location leads only, not source identity proofs.'},indent=2)+'\n')
print('scanned',len(fs),'matching module signatures',len(found),'R1FirstFold hash',hashhits)
for m,rows in found.items():print(m,len(rows),[x['path'] for x in rows[:3]])
