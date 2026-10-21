#!/usr/bin/env python3
"""Same reversible explicit-Ops adaptation as the compact caller packet."""
from pathlib import Path
import re,json,hashlib,sys
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True)
raw=(I/'Types.lean').read_text();assert 'import AspisS2OwnedStage1.TypesExternal' not in raw
t=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',raw,flags=re.M)
adapters=[]
names=re.findall(r'^inductive ([A-Za-z0-9_.]+) where',t,re.M)
for name in names:
 pat=r'(@\[[^\]]*\]\n)inductive '+re.escape(name)+r' where\n((?:\|[^\n]*\n(?:  [^\n]*\n)*)+)'
 m=re.search(pat,t);assert m,name
 attr=m[1].replace('discriminant isize, ','').replace('@[discriminant isize]\n','')
 rows=[]
 for row in re.finditer(r'^\| ([A-Za-z0-9_]+) :([\s\S]*?)(?=^\||\Z)',m[2],re.M):rows.append((row[1],row[2].count('→')))
 decl='\ndef '+name+'.read_discriminant (x : '+name+') : Isize :=\n  match x with\n'
 for n,(c,args) in enumerate(rows):decl+='  | .'+c+(' _'*args)+' => '+str(n)+'#isize\n'
 decl+='\ninstance _root_.AspisS2OwnedStage1.'+name+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+name+' Isize where\n  read_discriminant := '+name+'.read_discriminant\n'
 before=m[0];after=attr+'inductive '+name+' where\n'+m[2]+decl;t=t.replace(before,after)
 adapters.append(dict(name=name,before=before,after=after,codes=dict((c,n) for n,(c,_) in enumerate(rows))))
t+='\n#print axioms AspisS2OwnedStage1.solana_program_error.ProgramError\n'
(O/'S2OwnedStage1TypesV1.lean').write_text(t)
fraw=(I/'Funs.lean').read_text();f=fraw.replace('import AspisS2OwnedStage1.Types','import S2OwnedStage1TypesV1').replace('import AspisS2OwnedStage1.FunsExternal\n','')
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
external=(I/'FunsExternal_Template.lean').read_text()
blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',external,re.M)
mapping={};fields=[]
for i,(name,typ) in enumerate(blocks):
 typ=typ.strip();field='op'+str(i);mapping[name]=field
 if typ.startswith('{'):
  typ='∀ '+typ;depth=0;k=0
  for j,ch in enumerate(typ):
   if ch in '({':depth+=1
   elif ch in ')}':depth-=1
   elif ch==':' and depth==0:k=j;break
  assert k;typ=typ[:k].rstrip()+', '+typ[k+1:].lstrip()
 else:assert typ.startswith(':'),(name,typ);typ=typ[1:].strip()
 fields.append('  '+field+' : '+typ.replace('\n','\n    '))
f=f.replace('namespace AspisS2OwnedStage1\n','namespace AspisS2OwnedStage1\n\nstructure Ops where\n'+'\n'.join(fields)+'\n\n',1)
def mentions(txt,n):return bool(re.search(r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])',txt))
for name in sorted(mapping,key=len,reverse=True):f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','ops.'+mapping[name],f)
decls=list(re.finditer(r'\bdef\s+([A-Za-z0-9_.]+)',fraw));chunks={m[1]:fraw[m.end():decls[i+1].start() if i+1<len(decls) else len(fraw)] for i,m in enumerate(decls)}
changed={n for n,c in chunks.items() if any(mentions(c,x) for x in mapping)}
while True:
 more={n for n,c in chunks.items() if any(mentions(c,x) for x in changed)}
 if more<=changed:break
 changed|=more
for name in sorted(changed,key=len,reverse=True):
 f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','('+name+' ops)',f)
 f=re.sub(r'def\s+\('+re.escape(name)+r' ops\)','def '+name+' (ops : Ops)',f)
f+='\n#print axioms AspisS2OwnedStage1.owned_stage1_tail\n#print axioms AspisS2OwnedStage1.owned_checkpoint_nonzero\n'
(O/'S2OwnedStage1ModelV1.lean').write_text(f)
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
(O/'owned-stage1-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(raw),raw_funs_sha256=sha(fraw),external_sha256=sha(external),types_sha256=sha(t),model_sha256=sha(f),boundaries=mapping,discriminants=adapters,changes=['remove generated resource settings','qualify enum discriminant instances with unchanged codes','explicit complete Ops signatures in place of external function template axioms','Ops threaded only to consumers'],qualification='Complete owned reference emission; SDK IO and child implementations remain explicit. No TypesExternal or FunsExternal axiom imported.'),indent=2)+'\n')
print(json.dumps(dict(boundaries=mapping,types=len(names))))
