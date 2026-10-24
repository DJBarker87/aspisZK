#!/usr/bin/env python3
"""Generate full bijections only after checking every field and constructor."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
cut=S/'S6FullForestEncoderNamedTypesV1.lean';native=B/'lean/bridge-decoder-public-20261016/AspisR1TerminalDecoder/Types.lean'
def parse(path):
 s=re.sub(r'/[-*][\s\S]*?[-*]/','',path.read_text());s=re.sub(r'(?m)^--[^\n]*\n','',s);s=re.sub(r'(?m)^@\[[^\n]*\]\n','',s)
 matches=list(re.finditer(r'(?m)^(structure|inductive) ([\w.]+)\s+where',s));rows={}
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else s.index('\nend ',m.end())
  body=s[m.end():end].strip();body=body.split('\n#print')[0].strip()
  pattern=r'(?m)^  (\w+)\s*:' if m[1]=='structure' else r'(?m)^\| (\w+)\s*:'
  # Preserve indentation for record fields.
  body=re.split(r'(?m)^(?:def|instance|theorem|end|namespace|#print)\b',s[m.end():end],maxsplit=1)[0]
  fields=list(re.finditer(pattern,body));items=[]
  for j,f in enumerate(fields):
   stop=fields[j+1].start() if j+1<len(fields) else len(body)
   sig=' '.join(body[f.end():stop].split())
   items.append((f[1],sig))
  assert items,m[2];rows[m[2]]=dict(kind=m[1],items=items)
 return rows
c=parse(cut);n=parse(native);norm=lambda s:re.sub(r'\s+','',s.replace('aspis_statement.',''))
native_name=lambda q:q.replace('aspis_statement.','')
for q,row in c.items():
 other=n[native_name(q)]
 assert row['kind']==other['kind'] and [x[0] for x in row['items']]==[x[0] for x in other['items']],q
 for (_,a),(_,b) in zip(row['items'],other['items']):assert norm(a)==norm(b),(q,a,b)
leaf=lambda q:q.split('.')[-1]
CN='AspisS6FullForestEncoderNamed.';NN='AspisR1TerminalDecoder.'
map_expr=lambda direction,ty,x:(direction+leaf(ty)+' ('+x+')') if ty in c else x
out='import S6FullForestEncoderNamedTypesV1\nimport S6NativeLateCodecV1\nset_option autoImplicit false\nopen Aeneas Aeneas.Std\nnamespace AspisS6OuterCarrierBridge\n\n'
prior=[]
for q,row in c.items():
 name=leaf(q);nt=native_name(q)
 for direction,src,dst in [('to',CN+q,NN+nt),('from',NN+nt,CN+q)]:
  out+='def '+direction+name+' (value : '+src+') : '+dst+' :=\n'
  if row['kind']=='structure':
   out+='  {'+','.join(field+':='+map_expr(direction,ty,'value.'+field) for field,ty in row['items'])+'}\n\n'
  else:
   out+='  match value with\n'
   for ctor,sig in row['items']:
    parts=[s.strip() for s in sig.split('→')];assert parts[-1]==q,(q,ctor,parts)
    args=['x'+str(i) for i in range(len(parts)-1)]
    out+='  | .'+ctor+(' '+' '.join(args) if args else '')+' => '+dst+'.'+ctor+(' '+' '.join('('+map_expr(direction,ty,x)+')' for ty,x in zip(parts[:-1],args)) if args else '')+'\n'
   out+='\n'
 for direction,src in [('from_to',CN+q),('to_from',NN+nt)]:
  expr='from'+name+' (to'+name+' value)' if direction=='from_to' else 'to'+name+' (from'+name+' value)'
  lemmas=','.join([direction+leaf(x) for x in prior])
  out+='@[simp] theorem '+direction+name+' (value : '+src+') : '+expr+'=value := by\n'
  out+='  cases value <;> simp only [to'+name+',from'+name+(','+lemmas if lemmas else '')+']\n  all_goals rfl\n\n'
 out+='def equiv'+name+' : '+CN+q+' ≃ '+NN+nt+' where\n  toFun := to'+name+'\n  invFun := from'+name+'\n  left_inv := from_to'+name+'\n  right_inv := to_from'+name+'\n\n#print axioms equiv'+name+'\n\n'
 prior.append(q)
out+='end AspisS6OuterCarrierBridge\n';p=S/'S6OuterCarrierBridgeV1.lean';meta=dict(schema='focused-extractor-proof-packet-v1',cut_types_sha256=hashlib.sha256(cut.read_bytes()).hexdigest(),native_types_sha256=hashlib.sha256(native.read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),full_declarations=len(c),fields_and_constructors=c,qualification='Schema checks gate generation; kernel full inverse functions establish actual complete nominal-carrier bijections. This alone does not install callees, prove outer body correspondence or close S6.')
m=E/'s6-outer-carrier-bridge-generation.json'
if '--check' in sys.argv:assert p.read_text()==out and json.loads(m.read_text())==json.loads(json.dumps(meta))
else:p.write_text(out);m.write_text(json.dumps(meta,indent=2)+'\n')
