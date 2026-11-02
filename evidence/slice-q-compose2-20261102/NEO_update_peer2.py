"""Layer changed committed sibling blobs over the retained initial import."""
from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='37638ac1be595801ab9b20957a104bd5126cbb6f';PREFIX='evidence/slice-q-mul2-20261101/'
old=json.loads((E/'NEO_NEI_PROVENANCE.json').read_text());assert old['revision']=='1dbf5ad1511b14687a27a2e5043ed50a8515547c'
(E/'NEO_NEI_PROVENANCE_002.json').write_text(json.dumps(old,indent=1)+'\n')
proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
manifest={};changed={}
for line in subprocess.check_output(['git','ls-tree','-rl',REV,'--',PREFIX],cwd=R,text=True).splitlines():
 meta,path=line.split('\t');_,kind,blob,size=meta.split();assert kind=='blob'
 if old['files'].get(path,{}).get('git_blob')==blob:manifest[path]=old['files'][path];continue
 proc.stdin.write((blob+'\n').encode());proc.stdin.flush();head=proc.stdout.readline().split();raw=proc.stdout.read(int(head[2]));assert proc.stdout.read(1)==b'\n'
 try:changed[path]=raw.decode()
 except UnicodeDecodeError:changed[path]=dict(base64=base64.b64encode(raw).decode())
 manifest[path]=dict(sha256=hashlib.sha256(raw).hexdigest(),git_blob=blob,bytes=len(raw))
proc.stdin.close();proc.wait()
groups=[];group={};size=0
for name,value in changed.items():
 n=len(json.dumps(value))
 if size+n>50*1024**2 and group:groups.append(group);group={};size=0
 group[name]=value;size+=n
if group:groups.append(group)
chunks=old['archives'].copy()
for i,data in enumerate(groups,3):
 name=f'NEO_NEI_UPDATE.{i:03}.json';raw=json.dumps(data,sort_keys=True,separators=(',',':')).encode();blob=lzma.compress(raw,preset=6);assert len(blob)<20*1024**2
 (E/(name+'.xz')).write_bytes(blob);(E/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'  '+name+'\n')
 chunks.append(dict(path=name+'.xz',sha256=hashlib.sha256(blob).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),files=len(data),role='update'))
new=dict(old,revision=subprocess.check_output(['git','rev-parse',REV],cwd=R,text=True).strip(),base_revision=old['revision'],archives=chunks,files=manifest,updated_paths=sorted(changed),deleted_paths=sorted((set(old.get('deleted_paths',[]))|set(old['files']))-set(manifest)),policy='Git-only layered import; old inputs retained in original archives; overwritten current blobs and deletions explicit; never read sibling live worktree')
(E/'NEO_NEI_PROVENANCE.json').write_text(json.dumps(new,indent=1)+'\n')
print(len(changed),'changed/new blobs in',len(groups),'new archives')
