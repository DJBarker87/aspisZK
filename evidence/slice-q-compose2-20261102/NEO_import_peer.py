"""Archive committed sibling inputs only; never access the sibling live worktree."""
from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='66c32b9242';PREFIX='evidence/slice-q-mul2-20261101/'
proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
files={};manifest={}
for line in subprocess.check_output(['git','ls-tree','-rl',REV,'--',PREFIX],cwd=R,text=True).splitlines():
 meta,path=line.split('\t');oid,kind,blob,size=meta.split();assert kind=='blob'
 proc.stdin.write((blob+'\n').encode());proc.stdin.flush();head=proc.stdout.readline().split();raw=proc.stdout.read(int(head[2]));assert proc.stdout.read(1)==b'\n'
 files[path]=raw.decode();manifest[path]=dict(sha256=hashlib.sha256(raw).hexdigest(),git_blob=blob,bytes=len(raw))
proc.stdin.close();proc.wait()
archives=[];group={};size=0
for path,data in files.items():
 if size+len(data.encode())>50*1024**2 and group:
  archives.append(group);group={};size=0
 group[path]=data;size+=len(data.encode())
if group:archives.append(group)
chunks=[]
for i,group in enumerate(archives,1):
 name=f'NEO_NEI_INPUTS.{i:03}.json';raw=json.dumps(group,sort_keys=True,separators=(',',':')).encode()
 blob=lzma.compress(raw,preset=6);assert len(blob)<20*1024**2
 (E/(name+'.xz')).write_bytes(blob);(E/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'  '+name+'\n')
 chunks.append(dict(path=name+'.xz',sha256=hashlib.sha256(blob).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),files=len(group)))
(E/'NEO_NEI_PROVENANCE.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse',REV],cwd=R,text=True).strip(),branch='codex/cx-slice-q-mul2-20261029',source_prefix=PREFIX,archives=chunks,files=manifest,policy='Copied Git blobs, no live worktree, no proof duplication. Proposals gain no credit until replay and K-3/K-2 closure audit.'),indent=1)+'\n')
for n in ['NEO_NEI_INPUTS.json.xz','NEO_NEI_INPUTS.json.sha256']:
 (E/n).unlink(missing_ok=True)
print(len(files),'files in',len(chunks),'sub-20MiB archives')
