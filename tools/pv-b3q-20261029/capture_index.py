from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library');rows=[]
for rel in ['core/src/array/mod.rs','core/src/slice/index.rs','core/src/slice/mod.rs','core/src/iter/adapters/enumerate.rs','core/src/slice/iter.rs','core/src/slice/iter/macros.rs']:
 p=root/rel;raw=p.read_bytes();s=raw.decode();items=[]
 for m in re.finditer(r'(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?(?:const\s+)?fn\s+(index_mut|index|as_mut_slice|as_slice|new|next|len|drop)\s*(?:<[^\n]*>)?\s*\(',s):
  a=m.start();b=s.find('{',m.end());semicolon=s.find(';',m.end())
  if 0<=semicolon<b:continue
  e=b+1;depth=1
  while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
  item=s[a:e];items.append(dict(name=m[1],line=s[:a].count('\n')+1,text=item,sha256=hashlib.sha256(item.encode()).hexdigest()))
 rows.append(dict(file=rel,path=str(p),file_sha256=hashlib.sha256(raw).hexdigest(),items=items))
(H/'deployed-index-sources.json').write_text(json.dumps(dict(toolchain='1.94.1',rows=rows),indent=2)+'\n')
for r in rows:
 print(r['file'])
 for i in r['items']:
  if i['name']in['index_mut','as_mut_slice','as_slice','len']:print(i['line'],i['text'][:1500])
