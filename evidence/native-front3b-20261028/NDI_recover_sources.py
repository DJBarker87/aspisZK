from pathlib import Path
import json,hashlib,subprocess,tarfile,lzma,io,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3b-20261028'
missing={}
for p in E.glob('NDI_*/receipt.json'):
 x=json.loads(p.read_text())
 for n,h in x.get('source_hashes',{}).items():
  local=p.parent/'sources'/n
  if local.exists():assert hashlib.sha256(local.read_bytes()).hexdigest()==h,(p,n)
  else:missing[p.parent.name+'/sources/'+n]=h
code='''from pathlib import Path
import json,hashlib,tarfile,sys,io
b=Path(B);missing=json.loads(MISSING)
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|xz') as t:
 for n,h in sorted(missing.items()):
  p=b/n;data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==h,(n,h)
  v=tarfile.TarInfo(n);v.size=len(data);v.mtime=0;t.addfile(v,io.BytesIO(data))
'''.replace('Path(B)','Path('+repr(B)+')').replace('json.loads(MISSING)','json.loads('+repr(json.dumps(missing))+')')
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code.encode(),capture_output=True)
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr.decode()
p=E/'NDI_receipt_sources.tar.xz';p.write_bytes(r.stdout);raw=lzma.decompress(r.stdout)
(E/'NDI_receipt_sources.tar.sha256').write_text(hashlib.sha256(raw).hexdigest()+'  NDI_receipt_sources.tar\n')
with tarfile.open(fileobj=io.BytesIO(raw)) as t:
 assert set(t.getnames())==set(missing)
 for n,h in missing.items():assert hashlib.sha256(t.extractfile(n).read()).hexdigest()==h
(E/'NDI_RECEIPT_SOURCE_ARCHIVE.json').write_text(json.dumps(dict(archive=p.name,archive_sha256=hashlib.sha256(r.stdout).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),files=missing,read_only_recovery=True),indent=2)+'\n')
print('recovered immutable snapshot files',len(missing),'compressed bytes',len(r.stdout))
