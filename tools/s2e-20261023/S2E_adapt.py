#!/usr/bin/env python3
"""Same reversible explicit-Ops adaptation as the compact caller packet."""
from pathlib import Path
import re,json,hashlib,sys
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True)
raw=(I/'Types.lean.txt').read_text();assert 'import S2E_Reference.TypesExternal' not in raw
# Reuse literally equal protocol carriers from the installed caller family.
R=Path(__file__).resolve().parents[2]
prior=(R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-tail-v8/generated/AspisS2OwnedStage1/Types.lean.txt').read_text()
def declarations(text):
 matches=list(re.finditer(r'^(structure|inductive|def) ([A-Za-z0-9_.]+)',text,re.M)); out={}
 for k,m in enumerate(matches):
  end=matches[k+1].start() if k+1<len(matches) else text.index('\nend ',m.end())
  doc=text.find('\n/--',m.end(),end)
  if doc!=-1:end=doc
  begin=text.rfind('/--',0,m.start())
  out[m[2]]=(text[begin:end].rstrip(),text[m.start():end].strip())
 return out
old=declarations(prior);fresh=declarations(raw);shared={};kept=[];adapters=[]
sdk_prior=(R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/generated/AspisS2SdkOwned/Types.lean.txt').read_text()
sdk_types=declarations(sdk_prior)
sdk_names={'OwnedAccount','OwnedDataCell','OwnedLamportsCell','OwnedSdk','LiveGuards'}
for name,(full,body) in fresh.items():
 if name.startswith(('aspis_core.','aspis_statement.','aspis_r1_cost_probe.','solana_program_error.')):
  assert name in old,name
  norm=lambda x:re.sub(r'\s+',' ',x).strip()
  assert norm(body)==norm(old[name][1]),('protocol carrier mismatch',name)
  shared[name]=hashlib.sha256(body.encode()).hexdigest()
 elif name.startswith('S2E_Reference.') and name.split('.')[-1] in sdk_names:
  short=name.split('.')[-1]
  norm=lambda text:re.sub(r'\s+',' ',text.replace('S2E_Reference.','')).strip()
  assert norm(body)==norm(sdk_types[short][1]),('SDK carrier mismatch',name)
  shared[name]=hashlib.sha256(body.encode()).hexdigest()
  kept.append('abbrev '+name+' := AspisS2OwnedStage1.SdkReference.'+short)
 else:kept.append(full)
t='import S2SdkOwnedTypesV1\nopen Aeneas Aeneas.Std Result ControlFlow Error AspisS2OwnedStage1\nnamespace S2E_Reference\n'+'\n\n'.join(kept)+'\nend S2E_Reference\n'
t+='\n#print axioms S2E_Reference.S2E_Reference.OwnedSdk\n'
(O/'S2E_Types.lean').write_text(t)
fraw=(I/'Funs.lean.txt').read_text();f=fraw.replace('import S2E_Reference.Types','import S2E_Types').replace('import S2E_Reference.FunsExternal\n','')
f=f.replace('open Aeneas Aeneas.Std Result ControlFlow Error','open Aeneas Aeneas.Std Result ControlFlow Error AspisS2OwnedStage1')
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
external=(I/'FunsExternal_Template.lean.txt').read_text()
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
f=f.replace('namespace S2E_Reference\n','namespace S2E_Reference\n\nstructure Ops where\n'+'\n'.join(fields)+'\n\n',1)
def mentions(txt,n):return bool(re.search(r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])',txt))
for name in sorted(mapping,key=len,reverse=True):f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','ops.'+mapping[name],f)
decls=list(re.finditer(r'\b(?:impl_def|def)\s+([A-Za-z0-9_.]+)',fraw));chunks={m[1]:fraw[m.end():decls[i+1].start() if i+1<len(decls) else len(fraw)] for i,m in enumerate(decls)}
changed={n for n,c in chunks.items() if any(mentions(c,x) for x in mapping)}
while True:
 more={n for n,c in chunks.items() if any(mentions(c,x) for x in changed)}
 if more<=changed:break
 changed|=more
for name in sorted(changed,key=len,reverse=True):
 f=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])','('+name+' ops)',f)
 f=re.sub(r'(impl_def|def)\s+\('+re.escape(name)+r' ops\)',lambda m:m[1]+' '+name+' (ops : Ops)',f)
# Expand the generated recursive default field definitionally after Ops threading.
f=f.replace('impl_def core.option.Option.Insts.CoreCmpPartialEqOption (ops : Ops)',
 'def core.option.Option.Insts.CoreCmpPartialEqOption (ops : Ops)')
f=f.replace('ne := core.cmp.PartialEq.ne.trait_default\n    ((core.option.Option.Insts.CoreCmpPartialEqOption ops) cmpPartialEqInst)',
 'ne := fun a b => do\n    let equal ← ops.op3 cmpPartialEqInst a b\n    ok (!equal)')
f+='\n#print axioms S2E_Reference.S2E_Reference.stage1\n#print axioms S2E_Reference.S2E_Reference.stage2\n'
(O/'S2E_Model.lean').write_text(f)
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
(O/'S2E-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(raw),raw_funs_sha256=sha(fraw),external_sha256=sha(external),types_sha256=sha(t),model_sha256=sha(f),boundaries=mapping,discriminants=adapters,shared_protocol_types=shared,changes=['remove generated resource settings','qualify enum discriminant instances with unchanged codes','explicit complete Ops signatures in place of external function template axioms','Ops threaded only to consumers'],qualification='Complete owned reference emission; SDK IO and child implementations remain explicit. No TypesExternal or FunsExternal axiom imported.'),indent=2)+'\n')
print(json.dumps(dict(boundaries=mapping,shared_protocol_types=len(shared))))
