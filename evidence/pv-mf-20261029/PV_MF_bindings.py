#!/usr/bin/env python3
"""Extract exact Aeneas Rust-name/source-location -> Lean declaration associations.
No generation hash chain is fabricated from a generated-file banner.
"""
import hashlib,json,re,subprocess
from pathlib import Path
D=Path(__file__).resolve().parent
# Use checker loader without invoking its command line.
import PV_MF_check as C
modules=C.load('MODULES.json');files=C.load('FILES.json')
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(h):
 proc.stdin.write((h+'\n').encode());proc.stdin.flush();hd=proc.stdout.readline().split();b=proc.stdout.read(int(hd[2]));proc.stdout.read(1);return b
tracked={}
for line in subprocess.check_output(['git','ls-tree','-r','85addf5a9764aa5e17d28bd6cf96bbda084447c5'],text=True).splitlines():
 meta,path=line.split('\t',1);tracked[path]=meta.split()[-1]
rust=[r['path'] for r in C.load('build-inputs.json') if r['path'].endswith('.rs')];out={};source_cache={};module_refs={}
for p,m in modules.items():
 if not any(x['text'].startswith(('    Source:','Source:','source:')) or 'Source:' in x['text'] for x in m['generated_source_annotations']):continue
 h=files[p]['git_blob'];module_refs[p]=h
 if h in out:continue
 s=blob(h).decode(errors='replace');rows=[]
 for z in re.finditer(r'/--((?:(?!-/).)*)-/\s*((?:@\[(?:(?!\]).)*\]\s*)*)(?:noncomputable\s+)?(?:def|abbrev|opaque|theorem)\s+([^\s({:]+)',s,re.S):
  comment=z[1];src=re.search(r"Source:\s*'([^']+\.rs)'(?:,\s*lines?\s+([^\n]+))?",comment)
  if not src:continue
  name=re.search(r'\[([^\n]+)\]',comment);original=src[1]
  # Longest exact path suffix, not first grep hit.
  opts=source_cache.get(original)
  for n in range(len(Path(original).parts),2,-1):
   if opts is not None:break
   suffix='/'.join(Path(original).parts[-n:]);opts=[r for r in rust if r==suffix or r.endswith('/'+suffix)]
   if opts:break
   opts=None
  opts=opts or []
  if original.startswith('/rustc/'):opts=[]
  source_cache[original]=opts
  rows.append({'lean_declaration':z[3],'rust_function':name[1] if name else None,'extraction_source_location':original,'line_span':src[2],'release_source_candidates':[{'path':r,'git_blob':tracked[r]} for r in opts], 'evidence_class':'extraction','generation_binding':'UNVERIFIED: origin hash chain and deployed-feature parity must be supplied; matching a name/location is insufficient'})
 if rows:out[h]=rows
# Split by module to respect artifact size limit.
parts=[];items=list(out.items())
for k in range(0,len(items),1):
 name=f'BINDINGS-part{k:03}.json';b=(json.dumps(dict(items[k:k+1]),indent=1)+'\n').encode();assert len(b)<20_000_000
 (D/name).write_bytes(b);parts.append({'path':name,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
(D/'BINDINGS.json').write_text(json.dumps({'sharded':parts,'kind':'dict'},indent=1)+'\n')
(D/'BINDING-MODULES.json').write_text(json.dumps(module_refs,indent=1)+'\n')
print(json.dumps({'extraction_module_paths':len(out),'declaration_associations':sum(map(len,out.values())),'module_paths':len(module_refs)}))
