#!/usr/bin/env python3
"""Exact old/new SDK type and Ops reuse for already-owned buffer reborrowing."""
from pathlib import Path
import re,json,sys,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';D=B/'lean-candidates/s126-caller-boundary-20261021';I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(exist_ok=True,parents=True)
t=(I/'Types.lean').read_text();fraw=(I/'Funs.lean').read_text();external=(I/'FunsExternal_Template.lean').read_text()
prior=(B/'evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/generated/AspisS2SdkOwned/Types.lean.txt').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def declarations(s):
 ms=list(re.finditer(r'^(structure|inductive|def) ([A-Za-z0-9_.]+)',s,re.M));rows={}
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else s.index('\nend ',m.end())
  doc=s.find('\n/--',m.end(),end)
  if doc!=-1:end=doc
  rows[m[2]]=s[m.start():end].strip()
 return rows
new=declarations(t);old=declarations(prior);assert set(new)==set(old),(set(new)-set(old),set(old)-set(new))
norm=lambda s:re.sub(r'\s+',' ',s).strip()
for name,body in new.items():assert norm(body)==norm(old[name]),name
namespace='AspisS2OwnedStage1.SdkReference.BorrowedReference'
f=fraw.replace('import AspisS2SdkOwned.Types','import S2SdkOwnedModelV1').replace('import AspisS2SdkOwned.FunsExternal\n','').replace('namespace AspisS2SdkOwned','namespace '+namespace).replace('end AspisS2SdkOwned','end '+namespace)
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',external,re.M)
fields=[];mapping={}
for index,(name,typ) in enumerate(blocks):
 typ=typ.strip();field='op'+str(index);mapping[name]=field
 if typ.startswith('{'):
  typ='∀ '+typ;depth=0;colon=0
  for j,ch in enumerate(typ):
   if ch in '({':depth+=1
   elif ch in ')}':depth-=1
   elif ch==':' and depth==0:colon=j;break
  assert colon;typ=typ[:colon].rstrip()+', '+typ[colon+1:].lstrip()
 else:assert typ.startswith(':'),(name,typ);typ=typ[1:].strip()
 fields.append('  '+field+' : '+typ.replace('\n','\n    '))
priorMapping=json.loads((D/'sdk-owned-emission-adapter.json').read_text())['boundaries']
assert mapping==priorMapping,(mapping,priorMapping)
expected='structure Ops where\n'+'\n'.join(fields)
priorModel=(D/'S2SdkOwnedModelV1.lean').read_text();actual=priorModel[priorModel.index('structure Ops where'):priorModel.index('\n/--',priorModel.index('structure Ops where'))]
assert norm(expected)==norm(actual),(expected,actual)
f=f.replace('namespace '+namespace+'\n','namespace '+namespace+'\n\n-- Literal-equal SDK types and twelve Ops fields are reused in full.\nabbrev Ops := AspisS2OwnedStage1.SdkReference.Ops\n\n',1)
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
f+='\n#print axioms '+namespace+'.owned_stage1\n'
(O/'S2SdkBorrowedReferenceV1.lean').write_text(f)
(O/'sdk-borrowed-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(t),raw_funs_sha256=sha(fraw),source_sha256=sha(f),shared_types={n:dict(source_sha256=sha(b),prior_sha256=sha(old[n]),normalized_body_equal=True) for n,b in new.items()},all_ops_fields_literal_equal=True,boundaries=mapping,qualification='Concrete already-owned buffer reborrowing candidate only. All thirty prior SDK/protocol types and the full twelve-field Ops are reused after literal-body checks. Original/new complete body and scan equivalence is a separate kernel gate; no production adoption or SDK caller correspondence is asserted.'),indent=2)+'\n')
