"""Archive committed sibling inputs and replay unchanged checks in own capsule.

Only NET parser recipes are eligible. Stopped inverse work is archived, not
credited. Capsule paths are transient reconstructions of committed archives.
"""
from pathlib import Path
import subprocess,json,hashlib,lzma,base64,sys,shutil
E=Path(__file__).resolve().parent;R=E.parent.parent
BRANCH='codex/cx-slice-q-compose3-20261102';PREFIX='evidence/slice-q-compose3-20261102/'
sha=lambda b:hashlib.sha256(b).hexdigest()
def archive():
 rev=subprocess.check_output(['git','rev-parse',BRANCH],cwd=R,text=True).strip()
 rows=subprocess.check_output(['git','ls-tree','-rl',rev,'--',PREFIX],cwd=R,text=True).splitlines()
 proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 chunks=[];data={};size=0;files={}
 def flush():
  nonlocal data,size
  if not data:return
  plain=json.dumps(data,separators=(',',':')).encode();raw=lzma.compress(plain,preset=6)
  name=f'NEV_NET_INPUTS.{len(chunks)+1:03}.json.xz';assert len(raw)<20*1024**2
  (E/name).write_bytes(raw);(E/(name.removesuffix('.xz')+'.sha256')).write_text(sha(plain)+'\n')
  chunks.append(dict(path=name,sha256=sha(raw),uncompressed_sha256=sha(plain),entries=len(data)))
  data={};size=0
 for line in rows:
  meta,path=line.split('\t');mode,kind,oid,n=meta.split();assert kind=='blob' and mode=='100644'
  proc.stdin.write((oid+'\n').encode());proc.stdin.flush();header=proc.stdout.readline();length=int(header.split()[2]);raw=proc.stdout.read(length);assert proc.stdout.read(1)==b'\n'
  if size+length>12*1024**2:flush()
  data[path]=base64.b64encode(raw).decode();size+=length
  files[path]=dict(git_blob=oid,bytes=length,sha256=sha(raw))
 flush();proc.stdin.close();proc.wait();assert proc.returncode==0
 (E/'NEV_NET_PROVENANCE.json').write_text(json.dumps(dict(revision=rev,branch=BRANCH,prefix=PREFIX,files=files,archives=chunks,credit_scope='Only NET complete CM/QM parser recipes and native same608-byte windows; all inverse WIP excluded'),indent=2)+'\n')
 print('archived',len(files),'files',len(chunks),'chunks',flush=True)
def replay():
 pins=json.loads((E/'NEV_NET_PROVENANCE.json').read_text());C=E/'.NEV_net_capsule';C.mkdir(exist_ok=True)
 target=C/PREFIX;target.mkdir(parents=True,exist_ok=True)
 restored=set()
 for chunk in pins['archives']:
  raw=(E/chunk['path']).read_bytes();assert sha(raw)==chunk['sha256'];plain=lzma.decompress(raw);assert sha(plain)==chunk['uncompressed_sha256']
  for name,encoded in json.loads(plain).items():
   assert name.startswith(PREFIX) and name not in restored;raw=base64.b64decode(encoded);pin=pins['files'][name]
   assert sha(raw)==pin['sha256'] and len(raw)==pin['bytes'];assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==pin['git_blob']
   p=C/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw);restored.add(name)
 assert restored==set(pins['files'])
 for d in (R/'evidence').iterdir():
  p=C/'evidence'/d.name
  if d.is_dir() and d.name not in [Path(PREFIX).name,E.name] and not p.exists():p.symlink_to(d.resolve(),target_is_directory=True)
 for name in ['docs','crates','programs','design','Cargo.lock','Cargo.toml']:
  p=C/name
  if not p.exists():p.symlink_to((R/name).resolve(),target_is_directory=(R/name).is_dir())
 outputs=[]
 for script in ['NET_validate.py','NET_tests.py']:
  r=subprocess.run([sys.executable,str(target/script)],cwd=C,capture_output=True,text=True)
  (E/('NEV_'+script.removesuffix('.py')+'_REPLAY.log')).write_text(r.stdout+r.stderr)
  outputs.append(dict(script=script,exit=r.returncode,source_sha256=sha((target/script).read_bytes())))
  if r.returncode:break
 (E/'NEV_NET_REPLAY.json').write_text(json.dumps(dict(revision=pins['revision'],capsule_reconstructed_from_committed_archives=True,outputs=outputs),indent=2)+'\n')
 print(outputs,flush=True)
 assert all(r['exit']==0 for r in outputs) and len(outputs)==2
if __name__=='__main__':
 if '--archive' in sys.argv:archive()
 else:replay()
