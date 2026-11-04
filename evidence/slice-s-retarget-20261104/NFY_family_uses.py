"""Exact S-root reachable symbols matched to source declarations, not import guesses."""
from pathlib import Path
import json,re,lzma,hashlib
E=Path(__file__).resolve().parent;D=json.loads((E/'NFY_DIAGNOSIS.json').read_text());G=json.loads((E/'NFY_SOURCE_GRAPH.json').read_text());P=json.loads((E/'NFY_PROVENANCE.json').read_text());A=json.loads((E/'NFY_AUDIT_ROOTS.json').read_text());ren=P['namespace_map'];pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(ren,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
reachable=set();pins=[]
for root in sorted(set(A['S_roots'])):
 group=next(i for i,ns in enumerate(A['groups']) if root in ns);p=E/f'NFY_NEP_proof{group}_{root}_REACHABLE.txt.xz';raw=lzma.decompress(p.read_bytes());reachable.update(raw.decode().splitlines());pins.append(dict(root=root,graph=p.name,sha256=hashlib.sha256(raw).hexdigest()))
def decls(src):
 stack=[]
 for i,line in enumerate(src.splitlines(),1):
  l=line.strip()
  m=re.match(r'namespace\s+([\w.]+)',l)
  if m:stack.append(('namespace',m[1]));continue
  if re.match(r'(?:noncomputable )?section(?: |$)',l):stack.append(('section',''));continue
  if re.match(r'end(?:\s|$)',l):
   if stack:stack.pop()
   continue
  m=re.search(r'(?:^|\]\s*)(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.]+)',l)
  if m:
   ns='.'.join(n for k,n in stack if k=='namespace');name=(ns+'.' if ns else '')+m[2]
   yield dict(line=i,kind=m[1],legacy_spelling=name,canonical_spelling=pat.sub(lambda m:ren[m.group()],name),source_line=line)
result={}
for family,info in D['families'].items():
 modules=[]
 for n in info['modules']:
  r=G[n];used=[]
  for d in decls(r.get('source','')):
   name=d['canonical_spelling'];matches=sorted(x for x in reachable if x==name or (d['kind'] in ['structure','inductive'] and x.startswith(name+'.')))
   if matches:used.append(dict(**d,reachable_symbols=matches))
  modules.append(dict(legacy_module=n,canonical_module=P['module_owner'].get(n,n),source_path=r['path'],source_sha256=hashlib.sha256(r['source'].encode()).hexdigest(),used_declarations=used))
 result[family]=dict(direct_affected_rows=info['rows'],modules=modules,used_declaration_count=sum(len(x['used_declarations']) for x in modules))
(E/'NFY_FAMILY_USES.json').write_text(json.dumps(dict(scope='94 selected S-root raw graphs; canonical actual reachable symbols matched to parsed source declarations. This is distinct from mere import dependence and does not assert legacy/canonical owner equality.',graphs=pins,families=result),indent=1)+'\n')
print(json.dumps({f:r['used_declaration_count'] for f,r in result.items()}))
