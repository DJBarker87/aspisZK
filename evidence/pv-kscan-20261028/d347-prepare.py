"""Resolve original receipt hashes before preparing private codegen inputs."""
import json,pathlib,hashlib,subprocess,collections,re
E=pathlib.Path(__file__).resolve().parent;C=pathlib.Path('/private/tmp/pv-kscan-cache-20261028');R='/home/dombarker/project-offloads/codex-pv-kscan-20261028'
ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());host=json.loads((C/'d347-host-sources.json').read_text());db={}
for p,v in host.items():db.setdefault(v['sha256'],dict(text=v['text'],origin=p,kind='retained host source'))
T=json.loads((C/'tree-index.json').read_text());wanted={p['pass_output'].split('/')[1] for p in ps};blobs={}
for tree in T.values():
 for p,b in tree.items():
  if (p.startswith('tools/') or p.startswith('evidence/') and p.split('/')[1] in wanted) and (p.endswith(('.rs','.rs.txt','.toml','.toml.txt','.lock','.lock.txt')) or p.endswith('/source.txt')):blobs.setdefault(b,p)
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for b,p in blobs.items():
 proc.stdin.write((b+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();data=proc.stdout.read(int(h[-1]));proc.stdout.read(1)
 sha=hashlib.sha256(data).hexdigest()
 db.setdefault(sha,dict(text=data.decode(errors='replace'),origin=p,blob=b,kind='committed exact evidence/source blob'))
(C/'d347-source-db.json').write_text(json.dumps(db))
plans=json.loads((E/'d347-plans.json').read_text());payload={};bindings=[]
def standalone(name,indices,filename):
 subset=[p for p in ps if p['index'] in indices];hashes={rs[p['receipt_blob']]['source_sha256'] for p in subset};assert len(hashes)==1
 sha=hashes.pop();v=db[sha];d=f'{R}/d347/{name}/package';f=d+'/'+filename;payload[f]=v['text']
 plans[name]=dict(command=['/home/dombarker/.cargo/bin/kani',f,'--only-codegen','--keep-temps','-j','4','--output-format','terse'],cwd=d,metadata_dirs=[d],harnesses=[p['harness'] for p in subset],source_checks={f:sha},indices=indices)
 bindings.append(dict(run=name,indices=indices,files=[dict(path=f,sha256=sha,**{k:v[k] for k in v if k!='text'})],basis='exact original receipt source_sha256'))
standalone('D002',list(range(62,71)),'PV_Inv_control.rs')
standalone('D003',list(range(71,77)),'PV_Inv_control.rs')
standalone('D004',list(range(77,83)),'PV_Inv_control.rs')
standalone('D005',list(range(83,94)),'PV_L2_native.rs')
# Zero receipts point to an explicitly retained source hash; group all original versions.
zg=collections.defaultdict(list)
for p in ps:
 if 94<=p['index']<=110:zg[rs[p['receipt_blob']]['source_sha256']].append(p['index'])
for n,indices in enumerate(zg.values(),6):standalone(f'D{n:03}',indices,'PV_L2_Zero_native.rs')
# Canonical control is a standalone Cargo package with a receipt-pinned lib.
name='D009';d=f'{R}/d347/{name}/package';orig='/home/dombarker/project-offloads/codex-pv-canon-20261027/control/';files=[]
for p,v in host.items():
 if p.startswith(orig):payload[d+'/'+p[len(orig):]]=v['text'];files.append(dict(path=d+'/'+p[len(orig):],sha256=v['sha256'],origin=p))
subset=[p for p in ps if 57<=p['index']<=61];assert all(rs[p['receipt_blob']]['source_sha256']==host[orig+'src/lib.rs']['sha256'] for p in subset)
plans[name]=dict(command=['/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',d+'/Cargo.toml','--lib','--only-codegen','--keep-temps','-j','4','--output-format','terse'],cwd=d,metadata_dirs=[f'{R}/d347/{name}/target'],harnesses=[p['harness'] for p in subset],source_checks={f['path']:f['sha256'] for f in files},indices=[p['index'] for p in subset]);bindings.append(dict(run=name,indices=plans[name]['indices'],files=files,basis='exact original receipt lib hash; retained Cargo manifest/lock'))
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(C/'d347-payload.json').write_text(json.dumps(payload));(E/'d347-source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n');print('source blobs',len(blobs),'hash db',len(db),'plans',len(plans),'zero groups',dict(zg))
