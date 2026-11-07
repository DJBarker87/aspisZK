from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger26-20261111';B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNK_20261111'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):(E/('NNK_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
old=J(P/'NNI_CLOSURE_PINS.json.xz');oldmods={r['module']for r in old['selected_objects']};roots=J(P/'NNI_AUDIT_ROOTS.json');extra=set()
for folder,n in [('tx1-principal-20261111','NNG_C137_AUDIT_ROOTS.json'),('tx1-principal-20261111','NNG_C087_AUDIT_ROOTS.json'),('tx2-auth-20261111','NMX_234_AUDIT_ROOTS.json')]:
 x=J(E.parent/folder/n);extra.update(x.get('roots',[]));extra.update(r for g in x['groups']for r in g)
new=sorted(extra-set(roots['roots']));groups=roots['groups']+[new[i:i+100]for i in range(0,len(new),100)]
put('AUDIT_ROOTS',dict(roots=sorted(set(roots['roots'])|extra),groups=groups));put('AUDIT_MODULES',[['NNK_COMBINED_IMPORT']]*len(groups))
seeds=[];paths=[]
x=J(P/'NNI_EXPORT.json');base=x['export']
for r in x['files']:seeds.append(dict(tag='NNI',path=r['path'],relative=r['path'][len(base)+1:],sha256=r['sha256']))
paths.append(B+'/NNI_seed')
# Snapshot the selected new modules from accepted candidate receipt, never a live worktree.
for folder,receipt,tag in [('tx1-principal-20261111','NNG_L619/receipt.json','NNG'),('tx2-auth-20261111','NMX_L1063/receipt.json','NMX')]:
 x=J(E.parent/folder/receipt);env=x['env']['LEAN_PATH'].split(':');pins=x['deps_fingerprint']['selected_objects']
 for r in pins.values():
  p=r['path'];root=next((q for q in env if p.startswith(q+'/')),None)
  if root is None:continue
  rel=p[len(root)+1:];m=rel.split('.olean')[0].removesuffix('.ir').replace('/','.')
  if m in oldmods:continue
  st=tag+str(env.index(root));seeds.append(dict(tag=st,path=p,relative=rel,sha256=r['sha256']))
 # receipt does not necessarily pin whole closure: append explicit retained export for new NMX modules.
 if tag=='NMX':
  z=J(E.parent/folder/'NMX_234_EXPORT.json');base=z['export']
  for r in z['files']:
   if r['module']in oldmods:continue
   seeds.append(dict(tag='NMXexport',path=r['path'],relative=r['path'][len(base)+1:],sha256=r['sha256']))
 paths += [B+'/'+s+'_seed'for s in dict.fromkeys(r['tag']for r in seeds if r['tag'].startswith(tag))]
# NNG receipt pins direct imports plus Aeneas only: take new objects in its committed combined import, pin on host before copy.
nng=J(E.parent/'tx1-principal-20261111/NNG_L619/receipt.json');src=(E.parent/'tx1-principal-20261111/NNG_C087_COMBINED.lean').read_text()
put('NNG_REQUIRED',dict(modules=[m for m in re.findall(r'^import ([\w.]+)',src,re.M)if m not in oldmods],paths=nng['env']['LEAN_PATH'].split(':')))
paths.insert(1,B+'/NNGextra_seed')
paths+=J(P/'NNI_PATHS.json');put('PATHS',list(dict.fromkeys(paths)));put('SEED_INPUTS',list({(r['tag'],r['relative']):r for r in seeds}.values()))
(E/'NNK_COMBINED_IMPORT.lean').write_text('import NNI_COMBINED_IMPORT\nimport NNG_C087_COMBINED\nimport NMX_R3_RegistryCombined\nimport LIB_VLib\nimport LIBB_V2Star\nimport LIBC_COMBINED_IMPORT\nimport RPx_Deployed\n#print axioms AspisR1.NNG_Candidate137.candidate\n#print axioms AspisR1.NNG_Candidate087.candidate\n#print axioms NMX_R3_DecoderFold.root\n#print axioms NMX_R3_RegistryRoot.root\n#print axioms AspisR1.RPx_Deployed.deployed\n')
for n in ['run','batch','pin','scope40','setup']:
 s=(P/('NNI_'+n+'.py')).read_text().replace('NNI_','NNK_')
 s=s.replace("E.parent/'ledger25-20261111/NMQ_CLOSURE_PINS.json.xz'","E.parent/'ledger26-20261111/NNI_CLOSURE_PINS.json.xz'")
 if n=='setup':s=s.replace('NMQ_20261111/NMQ_native/NMQ_ProofDriver','NNI_20261111/NNI_native/NNI_ProofDriver')
 (E/('NNK_'+n+'.py')).write_text(s)
(E/'NNK_Driver.lean').write_text((P/'NNI_Driver.lean').read_text().replace('NNI_','NNK_'))
expected={json.loads(l)['module']:json.loads(l)['imports']for l in(P/'NNI_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for folder in ['tx1-principal-20261111','tx2-auth-20261111','lib-20261111','libb-20261111','libc-20261111']:
 for p in(E.parent/folder).glob('*.lean'):
  if p.stem not in expected:expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
for p in E.glob('*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
(E/'NNK_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=k,imports=v))+'\n'for k,v in sorted(expected.items())))
put('PLAN',dict(basis_roots=len(roots['roots']),new_roots=len(new),groups=len(groups),budget=60,kani=0,extraction=0,gate='PENDING'))
print((E/'NNK_PLAN.json').read_text())
