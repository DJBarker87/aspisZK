from NMX_formal import *
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
selected={}
for r in rows:
 a=r.get('attempt','')
 if not a.startswith('NMX_L') or int(a[5:])<1072 or not r.get('module','').startswith('NMX_R4_') or r.get('module')=='NMX_R4_BindDiagnostic' or r.get('kind')!='lean' or r.get('exit_status')!=0 or not r.get('axioms_accepted',True):continue
 m=r['module'];p=E/(m+'.lean')
 if not p.exists() or sha(p.read_bytes()) not in r.get('source_hashes',{}).values():continue
 selected[m]=r
pairs=[]
for m,r in sorted(selected.items()):
 for line in r['print_axioms']:
  hit=re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  assert hit,(m,line)
  pairs.append((hit[1],m))
assert len(pairs)==len(set(pairs))
first=312;size=16;chunks=[pairs[i:i+size] for i in range(0,len(pairs),size)]
roots=[[] for _ in range(first)]+[[p[0] for p in chunk] for chunk in chunks]
mods=[[] for _ in range(first)]+[list(dict.fromkeys(p[1] for p in chunk)) for chunk in chunks]
(E/'NMX_R4_AUDIT_ROOTS.json').write_text(json.dumps(dict(first_new_group=first,groups=roots,scope='Only own current accepted R4 authentication source, total port and allocation roots; excludes diagnostic; no predecessor or all-roots audit'),indent=1)+'\n')
(E/'NMX_R4_AUDIT_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
(E/'NMX_R4_AUDIT_SELECTION.json').write_text(json.dumps({'modules':{m:{'attempt':r['attempt'],'source_sha256':sha((E/(m+'.lean')).read_bytes())} for m,r in selected.items()},'theorems':len(pairs),'groups':len(chunks),'roots':[p[0] for p in pairs]},indent=1)+'\n')
print(json.dumps(dict(modules=len(selected),theorems=len(pairs),groups=len(chunks))))
