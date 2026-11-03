"""Git-only incremental peer intake, never a sibling live-worktree read."""
from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;R=E.parent.parent;O=E.parent/'slice-q-compose2-20261102'
REV='5d12713bd3d7b813a911201357b22e2ef2d5acfa';PREFIX='evidence/slice-q-mul2-20261101/'
old=json.loads((O/'NEO_NEI_PROVENANCE.json').read_text());assert old['revision']=='37638ac1be595801ab9b20957a104bd5126cbb6f'
proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
manifest={};changed={}
for line in subprocess.check_output(['git','ls-tree','-rl',REV,'--',PREFIX],cwd=R,text=True).splitlines():
 meta,path=line.split('\t');_,kind,oid,size=meta.split();assert kind=='blob'
 if old['files'].get(path,{}).get('git_blob')==oid:manifest[path]=old['files'][path];continue
 proc.stdin.write((oid+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();raw=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n'
 try:changed[path]=raw.decode()
 except UnicodeDecodeError:changed[path]={'base64':base64.b64encode(raw).decode()}
 manifest[path]=dict(sha256=hashlib.sha256(raw).hexdigest(),git_blob=oid,bytes=len(raw))
proc.stdin.close();assert proc.wait()==0
groups=[];group={};size=0
for n,v in changed.items():
 sz=len(json.dumps(v))
 if size+sz>50*1024**2 and group:groups.append(group);group={};size=0
 group[n]=v;size+=sz
if group:groups.append(group)
archives=[dict(a,path='../slice-q-compose2-20261102/'+a['path']) for a in old['archives']]
for i,data in enumerate(groups,1):
 n=f'NET_NEI_UPDATE.{i:03}.json';raw=json.dumps(data,sort_keys=True,separators=(',',':')).encode();blob=lzma.compress(raw,preset=6);assert len(blob)<20*1024**2
 (E/(n+'.xz')).write_bytes(blob);(E/(n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 archives.append(dict(path=n+'.xz',role='update',sha256=hashlib.sha256(blob).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),files=len(data)))
p=dict(revision=REV,base_revision=old['revision'],base_provenance_sha256=hashlib.sha256((O/'NEO_NEI_PROVENANCE.json').read_bytes()).hexdigest(),source_prefix=PREFIX,files=manifest,archives=archives,updated_paths=sorted(changed),deleted_paths=sorted((set(old.get('deleted_paths',[]))|set(old['files']))-set(manifest)),policy='Git blobs only; new/WIP content receives no credit before strict replay and scoped support/caller audits')
(E/'NET_NEI_PROVENANCE.json').write_text(json.dumps(p,indent=1)+'\n');print(len(changed),'changed inputs in',len(groups),'archives')
