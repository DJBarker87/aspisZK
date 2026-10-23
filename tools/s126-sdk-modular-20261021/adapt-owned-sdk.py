#!/usr/bin/env python3
"""Explicit-Ops SDK-state emission; reuse byte-identical protocol declarations.
No external template/axiom is imported. New owned heap/guard state is retained
in full, and all standard helper bodies in the generated Funs remain present.
"""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True)
old=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-tail-v8/generated/AspisS2OwnedStage1/Types.lean.txt'
raw=(I/'Types.lean').read_text();prior=old.read_text();assert 'TypesExternal' not in raw
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def declarations(s):
 matches=list(re.finditer(r'^(structure|inductive|def) ([A-Za-z0-9_.]+)',s,re.M));out={}
 for k,m in enumerate(matches):
  end=matches[k+1].start() if k+1<len(matches) else s.index('\nend ',m.end())
  doc=s.find('\n/--',m.end(),end)
  if doc!=-1:end=doc
  begin=s.rfind('/--',0,m.start())
  out[m[2]]=(s[begin:end].rstrip(),s[m.start():end].strip())
 return out
fresh=declarations(raw);previous=declarations(prior);shared={};kept=[]
for name,(full,body) in fresh.items():
 if name.startswith(('aspis_core.','aspis_statement.','aspis_r1_cost_probe.','solana_program_error.')):
  assert name in previous,name
  norm=lambda b:re.sub(r'\s+',' ',b).strip()
  assert norm(body)==norm(previous[name][1]),('changed protocol declaration',name)
  shared[name]=dict(declaration_sha256=sha(body),prior_declaration_sha256=sha(previous[name][1]),normalized_body_equal=True)
 else:kept.append(full)
namespace='AspisS2OwnedStage1.SdkReference'
t='''-- Exact generated owned state declarations; protocol types are reused below.
import S2OwnedStage1TypesV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace '''+namespace+'\n\n'+'\n\n'.join(kept)+'\n\nend '+namespace+'\n'
t+='\n#print axioms '+namespace+'.OwnedSdk\n'
(O/'S2SdkOwnedTypesV1.lean').write_text(t)
fraw=(I/'Funs.lean').read_text();f=fraw.replace('import AspisS2SdkOwned.Types','import S2SdkOwnedTypesV1').replace('import AspisS2SdkOwned.FunsExternal\n','').replace('namespace AspisS2SdkOwned','namespace '+namespace).replace('end AspisS2SdkOwned','end '+namespace)
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
f=f.replace('namespace '+namespace+'\n','namespace '+namespace+'\n\nstructure Ops where\n'+'\n'.join(fields)+'\n\n',1)
def mentions(txt,name):return bool(re.search(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])',txt))
for name in sorted(mapping,key=len,reverse=True):f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','ops.'+mapping[name],f)
decls=list(re.finditer(r'\bdef\s+([A-Za-z0-9_.]+)',fraw));chunks={m[1]:re.sub(r'/\-[\s\S]*?\-/|--[^\n]*','',fraw[m.end():decls[i+1].start() if i+1<len(decls) else len(fraw)]) for i,m in enumerate(decls)}
changed={n for n,c in chunks.items() if any(mentions(c,x) for x in mapping)}
while True:
 more={n for n,c in chunks.items() if any(mentions(c,x) for x in changed)}
 if more<=changed:break
 changed|=more
for name in sorted(changed,key=len,reverse=True):
 f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','('+name+' ops)',f)
 f=re.sub(r'def\s+\('+re.escape(name)+r' ops\)','def '+name+' (ops : Ops)',f)
f+='\n#print axioms '+namespace+'.owned_stage1\n#print axioms '+namespace+'.owned_release_guards\n'
(O/'S2SdkOwnedModelV1.lean').write_text(f)
(O/'sdk-owned-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(raw),raw_funs_sha256=sha(fraw),prior_raw_types_sha256=sha(prior),external_sha256=sha(external),types_sha256=sha(t),model_sha256=sha(f),shared_declarations=shared,kept_declarations=[n for n in fresh if n not in shared],boundaries=mapping,changes=['remove generated resource options','reuse only identical protocol declarations from checked S2 types','retain every owned SDK/guard state field and generated function body','replace external function template by complete explicit Ops signatures','thread Ops only through consumers'],qualification='Owned full SDK-state reference emission, not actual SDK conformance. No SDK-read callbacks are retained. Representation validity, concrete SDK operation instances and enclosing source/trace join remain to be proved.'),indent=2)+'\n')
print(json.dumps(dict(shared_types=len(shared),new_types=len(kept),boundaries=mapping)))
