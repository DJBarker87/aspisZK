#!/usr/bin/env python3
"""Mechanical parameterization of Aeneas external templates, with no axioms.
No function body, branch, child order, argument or error mapping is erased.
"""
from pathlib import Path
import re,json,hashlib,sys
from repair_layout import repair
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True)
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
t=(I/'Types.lean.txt').read_text();external_types=(I/'TypesExternal_Template.lean.txt').read_text() if (I/'TypesExternal_Template.lean.txt').exists() else ''
assert 'import AdapterRw.TypesExternal' not in t or not re.search(r'^axiom\b',external_types,re.M),'Include opaque enum/type layouts in Charon before adaptation'
t=t.replace('import AdapterRw.TypesExternal\n','')
t=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',t,flags=re.M)
t=t.replace('@[discriminant','@[import_union_discriminant').replace('import Aeneas\n','import Aeneas\nimport ImportUnionNamedDiscriminant\n')
(O/'AdapterRwTypes.lean').write_text(t)
fraw=(I/'Funs.lean.txt').read_text();f=repair(fraw).replace('import AdapterRw.Types','import AdapterRwTypes').replace('import AdapterRw.FunsExternal\n','')
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
ext=(I/'FunsExternal_Template.lean.txt').read_text();blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',ext,re.M)
mapping={};fields=[]
for i,(name,typ) in enumerate(blocks):
 typ=typ.strip();field='op'+str(i);mapping[name]=field
 if not typ.startswith(':'):
  depth=0;colon=None
  for j,ch in enumerate(typ):
   if ch in '({':depth+=1
   elif ch in ')}':depth-=1
   elif ch==':' and depth==0:colon=j;break
  assert colon is not None,(name,typ)
  typ='∀ '+typ[:colon].rstrip()+', '+typ[colon+1:].lstrip()
 else:typ=typ[1:].strip()
 fields.append('  '+field+' : '+typ.replace('\n','\n    '))
f=f.replace('namespace AdapterRw\n','namespace AdapterRw\n\nstructure Ops where\n'+'\n'.join(fields)+'\n\n',1)
pat=lambda name:r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])'
mentions=lambda text,name:bool(re.search(pat(name),text))
for name in sorted(mapping,key=len,reverse=True):f=re.sub(pat(name),'ops.'+mapping[name],f)
decls=list(re.finditer(r'\b(?:impl_def|def)\s+([A-Za-z0-9_.]+)',fraw));chunks={m[1]:fraw[m.end():decls[i+1].start() if i+1<len(decls) else len(fraw)] for i,m in enumerate(decls)}
changed={n for n,c in chunks.items() if any(mentions(c,x) for x in mapping)}
while True:
 more={n for n,c in chunks.items() if any(mentions(c,x) for x in changed)}
 if more<=changed:break
 changed|=more
for name in sorted(changed,key=len,reverse=True):
 f=re.sub(pat(name),'('+name+' ops)',f)
 f=re.sub(r'(impl_def|def)\s+\('+re.escape(name)+r' ops\)',lambda m:m[1]+' '+name+' (ops : Ops)',f)
# Definitionally expand the single Option equality recursive default.
f=f.replace('impl_def core.option.Option.Insts.CoreCmpPartialEqOption (ops : Ops)','def core.option.Option.Insts.CoreCmpPartialEqOption (ops : Ops)')
optioneq=mapping.get('core.option.Option.Insts.CoreCmpPartialEqOption.eq')
if optioneq:
 f=f.replace('ne := core.cmp.PartialEq.ne.trait_default\n    ((core.option.Option.Insts.CoreCmpPartialEqOption ops) cmpPartialEqInst)',f'ne := fun a b => do\n    let equal ← ops.{optioneq} cmpPartialEqInst a b\n    ok (!equal)')
f+='\n#print axioms AdapterRw.observer\n#print axioms AdapterRw.r1_pool_adapter.owned.stage1_owned\n#print axioms AdapterRw.r1_pool_adapter.owned.stage2_owned\n'
assert not re.search(r'^axiom\b',f,re.M)
(O/'AdapterRwModel.lean').write_text(f)
(O/'AdapterRw-emission-adapter.json').write_text(json.dumps({'raw_types_sha256':sha((I/'Types.lean.txt').read_text()),'raw_funs_sha256':sha(fraw),'types_sha256':sha(t),'model_sha256':sha(f),'boundaries':mapping,'ops_consumers':sorted(changed),'changes':['repair clipped column68 whitespace only, token equality checked','rename generated imports','replace old discriminant attribute with named import-union adapter, unchanged codes','remove generated resource settings','replace every external template axiom with an explicit complete Ops parameter','thread Ops transitively only to consumers','definitionally expand Option equality default'],'qualification':'exact complete caller emission with explicit uninstalled child/std/PDA/syscall operations; no production child or SDK effects proved merely by parameterization'},indent=2)+'\n')
print('external operations:',len(mapping))
