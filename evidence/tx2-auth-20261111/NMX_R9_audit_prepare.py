from NMX_formal import *
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
previous=set()
for f in ['NMX_R4_AUDIT_SELECTION.json','NMX_R6_AUDIT_SELECTION.json']:
 previous.update(json.loads((E/f).read_text())['roots'])
selected={}
for r in rows:
 a=r.get('attempt','');m=r.get('module','')
 if not a.startswith('NMX_L') or r.get('kind')!='lean' or r.get('exit_status')!=0 or not r.get('axioms_accepted',True):continue
 if not m.startswith(('NMX_R7_','NMX_R8_','NMX_R9_')) or any(s in m for s in ['Inspect','Diagnostic','Combined']):continue
 p=E/(m+'.lean')
 if not p.is_file() or sha(p.read_bytes()) not in r.get('source_hashes',{}).values():continue
 selected[m]=r
pairs=[]
for m,r in sorted(selected.items()):
 for line in r['print_axioms']:
  hit=re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",line);assert hit,(m,line)
  if hit[1] not in previous:pairs.append((hit[1],m))
assert len(pairs)==len(set(pairs))
first=325;size=16;chunks=[pairs[i:i+size] for i in range(0,len(pairs),size)]
roots=[[] for _ in range(first)]+[[p[0] for p in c] for c in chunks]
mods=[[] for _ in range(first)]+[list(dict.fromkeys(p[1] for p in c)) for c in chunks]
(E/'NMX_R9_AUDIT_ROOTS.json').write_text(json.dumps(dict(first_new_group=first,groups=roots,scope='Only own new current accepted stage-two source/port roots; excludes diagnostics, rejected shapes and prior119+73 audited roots'),indent=1)+'\n')
(E/'NMX_R9_AUDIT_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
(E/'NMX_R9_AUDIT_SELECTION.json').write_text(json.dumps(dict(modules={m:dict(attempt=r['attempt'],source_sha256=sha((E/(m+'.lean')).read_bytes())) for m,r in selected.items()},theorems=len(pairs),groups=len(chunks),roots=[p[0] for p in pairs],excluded_previous_roots=len(previous)),indent=1)+'\n')
print(json.dumps(dict(modules=len(selected),theorems=len(pairs),groups=len(chunks))))
