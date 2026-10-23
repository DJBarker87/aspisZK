#!/usr/bin/env python3
"""Reversible emission adaptation: concrete types, named Ops, enum names only."""
from pathlib import Path
import hashlib,json,re,sys
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(I/'Types.lean').read_text(); ext=(I/'TypesExternal_Template.lean').read_text() if (I/'TypesExternal_Template.lean').exists() else ''
assert not re.search(r'^axiom ',ext,re.M),'All original source types must be included before adapting.'
t=raw.replace('import AspisR1CurrentCaller.TypesExternal\n','')
t=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',t,flags=re.M)
adapters=[]
# The unqualified generated instance names collide for the source enums.
for match in list(re.finditer(r'(@\[[\s\S]*?\]\n)?inductive ([A-Za-z0-9_.]+) where\n((?:\|[^\n]*\n)+)',t)):
 pass
# Qualify generated enum instances; keep every constructor and discriminant code.
for name in ['aspis_core.r0.Error','verifier.Error','r1_wire.Error','verifier.Phase','transport.Variant','compact.CodecError','aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public']:
 pat=r'(@\[[^\]]*\]\n)inductive '+re.escape(name)+r' where\n((?:\|[^\n]*\n(?:  [^\n]*\n)*)+)'
 m=re.search(pat,t);assert m,name
 attr=m[1].replace('discriminant isize, ','').replace('@[discriminant isize]\n','')
 body='inductive '+name+' where\n'+m[2]
 rows=[]
 for row in re.finditer(r'^\| ([A-Za-z0-9_]+) :([\s\S]*?)(?=^\||\Z)',m[2],re.M):
  c,typ=row[1],row[2];args=typ.count('→');rows.append((c,args))
 decl='\ndef '+name+'.read_discriminant (x : '+name+') : Isize :=\n  match x with\n'
 for n,(c,args) in enumerate(rows):decl+='  | .'+c+(' _'*args)+' => '+str(n)+'#isize\n'
 decl+='\ninstance _root_.AspisR1CurrentCaller.'+name+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+name+' Isize where\n  read_discriminant := '+name+'.read_discriminant\n'
 before=m[0];after=attr+body+decl;assert t.count(before)==1;t=t.replace(before,after)
 adapters.append(dict(name=name,before=before,after=after,codes={c:i for i,(c,_) in enumerate(rows)}))
t += '\n#print axioms AspisR1CurrentCaller.verifier.Prepared\n#print axioms AspisR1CurrentCaller.r1_semantic.Verified\n'
(O/'CurrentCompactCallerTypesV1.lean').write_text(t)
fraw=(I/'Funs.lean').read_text();f=fraw.replace('import AspisR1CurrentCaller.Types','import CurrentCompactCallerTypesV1').replace('import AspisR1CurrentCaller.FunsExternal\n','')
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
external=(I/'FunsExternal_Template.lean').read_text()
# Each external becomes a field with its original complete dependent signature.
blocks=re.findall(r'^axiom ([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',external,re.M)
fields=[];mapping={}
for i,(name,typ) in enumerate(blocks):
 typ=typ.strip();field='op'+str(i);mapping[name]=field
 if typ.startswith('{'):
  # A field function retains implicit type arguments as an explicit forall.
  close=typ.index('}')+1;prefix=typ[:close];rest=typ[close:].strip()
  # All remaining binder groups are copied verbatim, through the return colon.
  typ='∀ '+prefix+' '+rest
  # Convert function declaration binder syntax to a Pi type.
  k=0;depth=0;quote=False
  for j,ch in enumerate(typ):
   if ch in '({':depth+=1
   elif ch in ')}':depth-=1
   elif ch==':' and depth==0:k=j;break
  assert k
  typ=typ[:k].rstrip()+', '+typ[k+1:].lstrip()
 else:
  assert typ.startswith(':'),(name,typ)
  typ=typ[1:].strip()
 fields.append('  '+field+' : '+typ.replace('\n','\n    '))
ops='structure Ops where\n'+'\n'.join(fields)+'\n\n'
f=f.replace('namespace AspisR1CurrentCaller\n','namespace AspisR1CurrentCaller\n\n'+ops,1)
for name in sorted(mapping,key=len,reverse=True):f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','ops.'+mapping[name],f)
decls=list(re.finditer(r'\bdef\s+([A-Za-z0-9_.]+)',fraw))
chunks={m[1]:fraw[m.end():decls[i+1].start() if i+1<len(decls) else len(fraw)] for i,m in enumerate(decls)}
def mentions(text,name):return bool(re.search(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])',text))
changed={n for n,c in chunks.items() if any(mentions(c,x) for x in mapping)}
while True:
 more={n for n,c in chunks.items() if any(mentions(c,x) for x in changed)}
 if more<=changed:break
 changed|=more
for name in sorted(changed,key=len,reverse=True):
 f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','('+name+' ops)',f)
 f=re.sub(r'def\s+\('+re.escape(name)+r' ops\)', 'def '+name+' (ops : Ops)', f)
# Inside emitted constants declarations, no external op is present. No new assumptions.
f += '\n#print axioms AspisR1CurrentCaller.verifier.candidate.prepare\n#print axioms AspisR1CurrentCaller.verifier.candidate.tx1\n#print axioms AspisR1CurrentCaller.verifier.mark\n'
(O/'CurrentCompactCallerModelV1.lean').write_text(f)
meta=dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(raw.encode()),raw_funs_sha256=sha(fraw.encode()),external_sha256=sha(external.encode()),types_sha256=sha(t.encode()),model_sha256=sha(f.encode()),boundaries=mapping,discriminant_names=adapters,changes=['import selected concrete source type module','remove generated resource settings','qualify seven potentially-colliding generated discriminant instances with identical codes','replace external operation declarations with explicit typed Ops fields','pass Ops through dependent functions'],scope='Complete emitted current compact prepare/tx1, actual carriers. Not an installation proof of retained child operations.')
(O/'caller-adapter.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'types':meta['types_sha256'],'model':meta['model_sha256'],'ops':len(mapping)}))
