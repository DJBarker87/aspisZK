"""Fetch retained records only; never relaunch a proof or audit."""
import pathlib,subprocess,shlex,json,hashlib,lzma
E=pathlib.Path('evidence/pv-lib-20261107/v1-coherence');V='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence';host='dombarker@100.108.41.90'
code=r'''
import pathlib,json,lzma,hashlib
V=pathlib.Path('HOST');E=V/'evidence'
files={str(p.relative_to(V)):p.read_text() for p in E.glob('*') if p.is_file() and p.suffix in ['.json','.log','.jsonl','.time']}
for p in E.glob('*.xz'):files[str(p.relative_to(V))]={'binary_hex':p.read_bytes().hex()}
for n in ['PLAN.json','INVENTORY.json','J.json']:
 files[n]=(V/n).read_text()
raw=json.dumps(files,sort_keys=True).encode();blob=lzma.compress(raw);(V/'COLLECTED_EVIDENCE.json.xz').write_bytes(blob)
print(json.dumps(dict(files=len(files),archive_sha256=hashlib.sha256(blob).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),archive_bytes=len(blob))))
'''.replace('HOST',V)
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr
manifest=json.loads(r.stdout);(E/'COLLECTED_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');subprocess.run(['scp',host+':'+V+'/COLLECTED_EVIDENCE.json.xz',str(E/'COLLECTED_EVIDENCE.json.xz')],check=True)
b=(E/'COLLECTED_EVIDENCE.json.xz').read_bytes();assert hashlib.sha256(b).hexdigest()==manifest['archive_sha256'];(E/'COLLECTED_EVIDENCE.json.sha256').write_text(manifest['uncompressed_sha256']+'\n');print(manifest)
