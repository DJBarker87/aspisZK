from NJN_transport import *
admission('NJN_NATIVE_SEED')
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});source=Path('/home/dombarker/project-offloads/codex-cx-entry-leaves-20261107/NJH_src');s=b/'NJN_src';assert not s.exists()
shutil.copytree(source,s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n in ['NIJ_src','NHY_src']:(b/n).symlink_to(s,target_is_directory=True)
print(json.dumps(dict(source=str(source),bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),free_bytes=shutil.disk_usage(b).free)))
''');assert r.returncode==0,r.stderr
(E/'NJN_NATIVE_SEED.json').write_text(r.stdout)
# Pin the successful Charon LLBC even though Aeneas failed. No outputs are discarded.
r=ssh('python3',f'''from pathlib import Path
import base64,lzma,json,hashlib
p=Path({B!r})/'NJN_reference.llbc';t=p.read_bytes();print(json.dumps(dict(data=base64.b64encode(lzma.compress(t)).decode(),sha256=hashlib.sha256(t).hexdigest(),bytes=len(t))))
''');assert r.returncode==0,r.stderr
import base64
x=json.loads(r.stdout);(E/'NJN_reference.llbc.xz').write_bytes(base64.b64decode(x.pop('data')));(E/'NJN_reference.llbc.sha256').write_text(x['sha256']+'\n');(E/'NJN_LLBC.json').write_text(json.dumps(x,indent=1)+'\n')
print('NJN native scratch copied; failed extraction LLBC retained')
