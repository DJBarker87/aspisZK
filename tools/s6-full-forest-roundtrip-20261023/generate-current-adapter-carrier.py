#!/usr/bin/env python3
"""Complete current adapter/native bijections, gated by full schema equality."""
from pathlib import Path
import re,json,hashlib,sys,runpy
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
args=sys.argv[:];sys.argv=[str(R/'tools/s6-full-forest-roundtrip-20261023/generate-outer-carrier-bridge.py'),'--check']
old=runpy.run_path(sys.argv[0]);sys.argv=args
# Strip complete multiline metadata before comparing fields/constructor types.
def parse(path):
 s=re.sub(r'/[-*][\s\S]*?[-*]/','',path.read_text());s=re.sub(r'(?m)^--[^\n]*\n','',s)
 s=re.sub(r'(?m)^@\[[\s\S]*?\]\s*\n','',s)
 matches=list(re.finditer(r'(?m)^(structure|inductive) ([\w.]+)\s+where',s));rows={}
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else s.index('\nend ',m.end())
  body=re.split(r'(?m)^(?:def|instance|theorem|end|namespace|#print)\b',s[m.end():end],maxsplit=1)[0]
  pattern=r'(?m)^  (\w+)\s*:' if m[1]=='structure' else r'(?m)^\| (\w+)\s*:'
  fields=list(re.finditer(pattern,body));items=[]
  for j,f in enumerate(fields):
   stop=fields[j+1].start() if j+1<len(fields) else len(body)
   items.append((f[1],' '.join(body[f.end():stop].split())))
  assert items,m[2];rows[m[2]]=dict(kind=m[1],items=items)
 return rows
adapter=S/'AdapterRwTypes.lean';a=parse(adapter)
c={q:row for q,row in old['c'].items() if not q.endswith('.PoolV1TransitionKind')}
for q,row in c.items():assert row==a[q],q
leaf=old['leaf'];native_name=old['native_name'];CN='AdapterRw.';NN='AspisR1TerminalDecoder.'
map_expr=lambda direction,ty,x:(direction+leaf(ty)+' ('+x+')') if ty in c else x
out='import AdapterRwTypes\nimport S6OuterNativeCodecV1\nset_option autoImplicit false\nopen Aeneas Aeneas.Std\nnamespace AspisS6CurrentAdapterCarrier\n\n'
prior=[]
for q,row in c.items():
 name=leaf(q);nt=native_name(q)
 for direction,src,dst in [('to',CN+q,NN+nt),('from',NN+nt,CN+q)]:
  out+='def '+direction+name+' (value : '+src+') : '+dst+' :=\n'
  if row['kind']=='structure':out+='  {'+','.join(field+':='+map_expr(direction,ty,'value.'+field) for field,ty in row['items'])+'}\n\n'
  else:
   out+='  match value with\n'
   for ctor,sig in row['items']:
    parts=[s.strip() for s in sig.split('→')];assert parts[-1]==q
    params=['x'+str(i) for i in range(len(parts)-1)]
    out+='  | .'+ctor+(' '+' '.join(params) if params else '')+' => '+dst+'.'+ctor+(' '+' '.join('('+map_expr(direction,ty,x)+')' for ty,x in zip(parts[:-1],params)) if params else '')+'\n'
   out+='\n'
 for direction,src in [('from_to',CN+q),('to_from',NN+nt)]:
  expr='from'+name+' (to'+name+' value)' if direction=='from_to' else 'to'+name+' (from'+name+' value)'
  lemmas=','.join([direction+leaf(x) for x in prior])
  out+='@[simp] theorem '+direction+name+' (value : '+src+') : '+expr+'=value := by\n'
  out+='  cases value <;> simp only [to'+name+',from'+name+(','+lemmas if lemmas else '')+']\n  all_goals rfl\n\n'
 out+='def equiv'+name+' : '+CN+q+' ≃ '+NN+nt+' where\n  toFun := to'+name+'\n  invFun := from'+name+'\n  left_inv := from_to'+name+'\n  right_inv := to_from'+name+'\n\n#print axioms equiv'+name+'\n\n'
 prior.append(q)
out+='end AspisS6CurrentAdapterCarrier\n'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=dict(schema='focused-extractor-proof-packet-v1',adapter_types_sha256=sha(adapter),native_types_sha256=sha(old['native']),complete_declarations=c,candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),qualification='All fields and error constructors, both inverse directions; absent independent transition-kind enum is not needed by these complete statement/error carriers. No SDK state/source-body equality inferred.')
p=S/'S6CurrentAdapterCarrierV1.lean';m=E/'s6-current-adapter-carrier-generation.json'
if '--check' in sys.argv:assert p.read_text()==out and json.loads(m.read_text())==json.loads(json.dumps(meta))
else:p.write_text(out);m.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(full_declarations=len(c))))
