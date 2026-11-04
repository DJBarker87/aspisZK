from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;R=E.parent.parent
ref='codex/cx-slice-q-compose4-20261104';rev=subprocess.check_output(['git','rev-parse',ref],cwd=R,text=True).strip()
rows=subprocess.check_output(['git','ls-tree','-r',rev,'evidence/slice-q-compose4-20261104'],cwd=R,text=True).splitlines()
files={};objects={}
for row in rows:
 meta,path=row.split('\t');oid=meta.split()[2];files[path]={'blob':oid};objects[oid]=None
p=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for oid in objects:
 p.stdin.write((oid+'\n').encode());p.stdin.flush();head=p.stdout.readline().decode().split();assert head[0]==oid and head[1]=='blob'
 raw=p.stdout.read(int(head[2]));assert p.stdout.read(1)==b'\n'
 try:content=raw.decode();encoding='utf8'
 except UnicodeDecodeError:content=base64.b64encode(raw).decode();encoding='base64'
 objects[oid]=dict(content=content,encoding=encoding,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
p.stdin.close();assert p.wait()==0
pack=dict(revision=rev,branch=ref,files=files,blobs=objects);raw=json.dumps(pack,separators=(',',':')).encode();compressed=lzma.compress(raw,preset=6)
assert len(compressed)<20*1024*1024
(E/'NFA_NEW_ARCHIVE.json.xz').write_bytes(compressed)
(E/'NFA_NEW_ARCHIVE.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'  NFA_NEW_ARCHIVE.json\n')
meta=dict(branch=ref,revision=rev,files=len(files),unique_blobs=len(objects),uncompressed_bytes=len(raw),compressed_bytes=len(compressed),raw_sha256=hashlib.sha256(raw).hexdigest(),compressed_sha256=hashlib.sha256(compressed).hexdigest(),method='Copied immutable committed blobs; no peer worktree access; no cherry-pick, merge or duplicated proof',revalidated=False)
(E/'NFA_NEW_PROVENANCE.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
