from pathlib import Path
import json,re,subprocess,hashlib,collections
E=Path(__file__).resolve().parent;p=E/'NNI_EXPECTED_IMPORTS.jsonl';expected={r['module']:r['imports']for r in map(json.loads,p.read_text().splitlines())};bad=json.loads((E/'NNI_SCAN_FINDINGS.json').read_text());assert all(not r['dangling']and not r['duplicate_owners']for r in bad)
files=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines();index=collections.defaultdict(list)
for file in files:
 if not file.endswith('.lean')or '/sources/'in file:continue
 index[Path(file).stem].append(file)
rows=[];unresolved=[]
for r in bad:
 m=r['module'];variants=collections.defaultdict(list)
 for file in index[m.split('.')[-1]]:
  b=subprocess.check_output(['git','show','HEAD:'+file]);imports=tuple(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',b.decode(),re.M)));variants[imports].append(dict(path=file,sha256=hashlib.sha256(b).hexdigest()))
 if len(variants)==1:
  imports,src=next(iter(variants.items()));expected[m]=list(imports);rows.append(dict(module=m,imports=list(imports),sources=src,method='all committed non-receipt source variants agree on imports; never copied from observed scan'))
 else:unresolved.append(dict(module=m,variants=[dict(imports=k,sources=v)for k,v in variants.items()]))
(E/'NNI_IMPORT_REPAIR_SOURCES.json').write_text(json.dumps(dict(resolved=rows,unresolved=unresolved),indent=1)+'\n')
p.write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
print('resolved',len(rows),'ambiguous/missing',len(unresolved));print([(r['module'],len(r['variants']))for r in unresolved])
