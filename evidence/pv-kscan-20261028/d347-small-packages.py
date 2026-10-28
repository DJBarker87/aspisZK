from pathlib import Path
import json,hashlib,re,subprocess,posixpath
E=Path(__file__).resolve().parent;C=Path('/private/tmp/pv-kscan-cache-20261028');R='/home/dombarker/project-offloads/codex-pv-kscan-20261028';db=json.loads((C/'d347-source-db.json').read_text());host=json.loads((C/'d347-host-sources.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());plans=json.loads((E/'d347-plans.json').read_text());bindings=json.loads((E/'d347-source-bindings.json').read_text());payload={}
def package(name,indices,original,overrides,basis):
 d=R+'/d347/'+name+'/package';files={p[len(original)+1:]:dict(text=v['text'],origin=p,kind='retained package source',sha256=v['sha256']) for p,v in host.items() if p.startswith(original+'/') and '/' not in p[len(original)+1:]};files.update(overrides)
 records=[]
 for rel,v in files.items():
  text=v['text'];text=text.replace(original+'/',d+'/')
  if rel=='Cargo.toml' or rel.endswith('.rs'):text=re.sub(r'(path\s*=\s*")([^"\n]+)(")',lambda m:m[1]+posixpath.normpath(original+'/'+m[2])+m[3] if m[2].startswith('../') else m[0],text)
  new=d+'/'+rel;payload[new]=text;records.append(dict(path=new,original_sha256=hashlib.sha256(v['text'].encode()).hexdigest(),sha256=hashlib.sha256(text.encode()).hexdigest(),origin=v['origin'],kind=v['kind']))
 subset=[p for p in ps if p['index'] in indices]
 plans[name]=dict(command=['/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',d+'/Cargo.toml','--lib','--only-codegen','--keep-temps','-j','4','--output-format','terse'],cwd=d,metadata_dirs=[R+'/d347/'+name+'/target'],harnesses=[p['harness'] for p in subset],source_checks={v['path']:v['sha256'] for v in records},indices=indices)
 bindings.append(dict(run=name,indices=indices,basis=basis,files=records))
def pinned(h):assert h in db,h;return db[h]
package('D026',[120,121],'/home/dombarker/project-offloads/codex-pv-cb-20261026/config-probe',{},'Exact original receipt input hashes matched retained config-probe package')
for name,indices in [('D027',[170,171]),('D028',[172,173,174])]:
 p=next(p for p in ps if p['index']==indices[0]);r=rs[p['receipt_blob']];overrides={f:pinned(h['sha256']) for f,h in r['source_snapshots'].items()};package(name,indices,'/home/dombarker/project-offloads/codex-pv-cbmid-20261027/source-proof',overrides,'Exact original source_snapshots hashes; only include-path and Cargo dependency-path relocation')
T=json.loads((C/'tree-index.json').read_text());tree={k:v for t in T.values() for k,v in t.items()}
def gitfile(path):
 blob=tree[path];b=subprocess.check_output(['git','cat-file','blob',blob]);return dict(text=b.decode(),origin=path,kind='committed per-run source snapshot',blob=blob)
for name,indices,orig in [('D029',[175,176,177],'/home/dombarker/project-offloads/codex-pv-join-20261026/pole4'),('D030',[178,179,180,181],'/home/dombarker/project-offloads/codex-pv-join-20261026/direct5')]:
 p=next(p for p in ps if p['index']==indices[0]);parent=p['receipt'].rsplit('/',1)[0];overrides={Path(k).name[:-4]:gitfile(k) for k in tree if k.startswith(parent+'/') and k.endswith(('.rs.txt','.toml.txt','.lock.txt'))};package(name,indices,orig,overrides,'Committed original per-run source snapshots; retained frozen aspis-core dependency')
f='evidence/pv-runjoin-20261026/os-contract/factory-kani/';package('D031',[196],'/home/dombarker/project-offloads/codex-pv-runjoin-20261026/factory-kani',{'lib.rs':gitfile(f+'lib-01.rs'),'Cargo.toml':gitfile(f+'Cargo-02.toml'),'Cargo.lock':gitfile(f+'Cargo-02.lock')},'Original run01 lib-01.rs and pre-libc-pin Cargo-02 manifest/lock; original PASS used libc 0.2.191 transitively, not later 0.2.186')
# pv6 was committed as the receipt-designated source snapshot after the runs.
rev=json.loads((E/'heads.json').read_text())['codex/pv-runjoin-20261026'];path='tools/pv-runjoin6-20261026/kani/lib.rs';b=subprocess.check_output(['git','show',rev+':'+path]);package('D032',list(range(208,218)),'/home/dombarker/project-offloads/codex-pv-runjoin-20261026/factory-kani',{'lib.rs':dict(text=b.decode(),origin=rev+':'+path,kind='receipt-designated committed original source snapshot')},'Receipt source_snapshot path at pinned branch head; original factory dependencies retained (libc 0.2.186, zeroize 1.9.1)')
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(E/'d347-source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n');(C/'d347-small-payload.json').write_text(json.dumps(payload));print('small packages prepared',len(payload))
