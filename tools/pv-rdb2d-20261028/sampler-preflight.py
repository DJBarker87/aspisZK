from pathlib import Path
import hashlib,json,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');old=json.loads(lzma.decompress((D/'final-dependency-fingerprint.json.xz').read_bytes()));env=json.loads((D/'env-J.json').read_text());roots=list(map(Path,env['LEAN_PATH'].split(':')));checks=[]
for x in old['canonical_ejr_objects']:
 rel=x['module'].replace('.','/')+'.olean';p=next((r/rel for r in roots if(r/rel).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 checks.append(dict(module=x['module'],source_sha256=x['source_sha256'],expected=x['object_sha256'],actual=h,path=str(p),ok=h==x['object_sha256']))
repairs={'AspisR72Sampler.Types','AspisR72Sampler.Funs'}
errors=[x for x in checks if not x['ok'] and x['module'] not in repairs]
r=dict(checks=checks,errors=errors,private_rebuilds=[x for x in checks if not x['ok'] and x['module'] in repairs],toolchain=env['ELAN_TOOLCHAIN'],LEAN_PATH=env['LEAN_PATH'],authority='RDB2C complete canonical EJR source/object fingerprint; canonical R72 sources rebuilt privately if absent or shadowed')
(D/'rdb2d-sampler-preflight.json').write_text(json.dumps(r,indent=2));print(json.dumps(dict(count=len(checks),errors=errors,private_rebuilds=r['private_rebuilds'])),flush=True);assert not errors
