from pathlib import Path
import json,hashlib,shutil,base64,lzma,subprocess,difflib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-claims-queryscan-20261108');S=B/'NJT_Q_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((P/'NJT_STAGING_MANIFEST.json').read_text());raw=lzma.decompress((P/'NJT_FROZEN_PAYLOAD.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(P/'NJT_FROZEN_PAYLOAD.json.sha256').read_text().strip();payload=json.loads(raw)
assert not S.exists();S.mkdir()
for n,v in manifest['files'].items():
 data=base64.b64decode(payload[n]);assert hashlib.sha256(data).hexdigest()==v['sha256'];p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
assert sha(B/'NJT_Q_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67';r=subprocess.run(['git','apply',str(B/'NJT_Q_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
n='crates/aspis-core/src/r0_transcript.rs';p=S/n;t=p.read_text();t+='\n'+(B/'NJT_Q_rank.rs.txt').read_text();p.write_text(t)
pins={n:sha(p),'KMX_stubs.rs':sha(S/'KMX_stubs.rs'),'KMX_native.rs':sha(S/'KMX_native.rs'),'KMX_CopyMeaning.lean':sha(S/'KMX_CopyMeaning.lean')}
frozen={n:v['sha256'] for n,v in manifest['files'].items() if n not in pins}
(B/'NJT_Q_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NJT_Q_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen));(B/'NJT_Q_NATIVE.patch').write_text(''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
(B/'NJT_Q_SETUP.json').write_text(json.dumps(dict(payload_sha256=hashlib.sha256(raw).hexdigest(),kmx_sha256=sha(B/'NJT_Q_KMX.patch'),files=len(manifest['files']),cargo_target_dir=str(B/'NJT_Q_target'),frozen_revision=manifest['revision']),indent=2)); print('query native scratch installed')
