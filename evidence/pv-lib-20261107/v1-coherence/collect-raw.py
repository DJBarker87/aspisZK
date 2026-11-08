"""Retain the actual final strict walk files, without re-running the walker."""
import pathlib,json,subprocess,shlex,hashlib,lzma
E=pathlib.Path(__file__).parent;V='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence';host='dombarker@100.108.41.90';roots=json.loads((E/'AUDIT_ROOTS.json').read_text())['roots']
code=r'''
import pathlib,json,hashlib,lzma,sys
V=pathlib.Path('HOST');expected=set(json.load(sys.stdin));D=V/'evidence/raw-audit';files=[];seen=set();digest=hashlib.sha256();dest=V/'RAW_GRAPH_ARCHIVE.json.xz'
with lzma.open(dest,'wb') as archive:
 def emit(b):digest.update(b);archive.write(b)
 emit(b'{');first=True
 for p in sorted(D.iterdir()):
  if not p.is_file():continue
  n=p.name
  if not n.startswith('NEP_pv-thread_'):continue
  matches={r for r in expected if n.startswith('NEP_pv-thread_'+r+'_')}
  if not matches:continue
  seen|=matches;b=p.read_bytes();files.append(dict(name=n,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
  if not first:emit(b', ')
  first=False;emit(json.dumps(n).encode());emit(b': ');emit(json.dumps(b.decode()).encode())
 emit(b'}')
assert seen==expected
print(json.dumps(dict(files=files,archive_bytes=dest.stat().st_size,archive_sha256=hashlib.file_digest(dest.open('rb'),'sha256').hexdigest(),uncompressed_sha256=digest.hexdigest())))
'''.replace('HOST',V)
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(roots),text=True,capture_output=True);assert r.returncode==0,r.stderr
m=json.loads(r.stdout);(E/'RAW_GRAPH_MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n');subprocess.run(['scp',host+':'+V+'/RAW_GRAPH_ARCHIVE.json.xz',str(E/'RAW_GRAPH_ARCHIVE.json.xz')],check=True);blob=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert hashlib.sha256(blob).hexdigest()==m['archive_sha256'];(E/'RAW_GRAPH_ARCHIVE.json.sha256').write_text(m['uncompressed_sha256']+'\n');print(len(m['files']),'actual graph files; compressed bytes',len(blob))

parts=[]
for j in range(0,len(blob),10*1024*1024):
 name=f'RAW_GRAPH_ARCHIVE.json.xz.part{j//(10*1024*1024):02d}';piece=blob[j:j+10*1024*1024];(E/name).write_bytes(piece);parts.append(dict(name=name,bytes=len(piece),sha256=hashlib.sha256(piece).hexdigest()))
m['parts']=parts;(E/'RAW_GRAPH_MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n');(E/'RAW_GRAPH_ARCHIVE.json.xz').unlink()
