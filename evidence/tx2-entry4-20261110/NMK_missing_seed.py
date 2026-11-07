from NMK_transport import *
import base64
admission('NMK_S004')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,lzma,base64
b=Path({B!r});src=b.parent/'codex-cx-tx2-common2-20261110/NLT_exports_final_20261110';rows=[]
for p in sorted(src.rglob('*')):
 if not p.is_file():continue
 q=b/'NMK_seed/NLT_full'/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert p.read_bytes()==q.read_bytes()
 else:shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(r['bytes'] for r in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NMK_NLT_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NMK_NLT_SEED.json.sha256').write_text(x['sha256']+'\n')
env=json.loads((E/'NMK_ENV.json').read_text());roots=env['LEAN_PATH'].split(':');roots += [B+'/NMK_seed/NLT_full'];roots +=json.loads((E.parent/'ledger24-20261110/NLX_PATHS.json').read_text());env['LEAN_PATH']=':'.join(dict.fromkeys(roots));(E/'NMK_ENV.json').write_text(json.dumps(env,indent=1));print(json.dumps(x))
