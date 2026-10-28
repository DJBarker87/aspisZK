from pathlib import Path
import subprocess,json,hashlib,tomllib,sys
b=Path(__file__).resolve().parent;s=b/'KNG_src';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';assert h(s/'Cargo.lock')==lock
features='aspis-r1-cost-probe/default,aspis-r1-cost-probe/private-leaf-salts,aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build'
cmd=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',str(s/'Cargo.toml'),'--locked','--offline','--format-version','1','--features',features]
r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0,r.stderr
m=json.loads(r.stdout);pk={p['id']:p for p in m['packages']};frozen=tomllib.loads((s/'Cargo.lock').read_text());allowed={(p['name'],p['version'],p.get('source')) for p in frozen['package']}
assert all((p['name'],p['version'],p.get('source')) in allowed for p in pk.values())
resolved=[dict(id=n['id'],name=pk[n['id']]['name'],version=pk[n['id']]['version'],source=pk[n['id']].get('source'),features=n['features'],deps=n['deps']) for n in m['resolve']['nodes']]
v=next(n for n in resolved if n['name']=='aspis-r1-cost-probe');assert set(v['features'])=={'default','private-leaf-salts','optimized-terminal','program-build'},v
st=next(n for n in resolved if n['name']=='aspis-statement');assert len(st['features'])==14 and 'r0' in st['features'] and 'pool-v1-kernel' in st['features'],st
assert h(s/'Cargo.lock')==lock
out=dict(command=cmd,lock_before=lock,lock_after=h(s/'Cargo.lock'),graph_validated_against_frozen_lock=True,resolved_features_per_crate=resolved)
(b/(sys.argv[1]+'-metadata.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
