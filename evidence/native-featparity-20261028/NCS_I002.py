from pathlib import Path
import subprocess,json,os,hashlib
w=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026/src')
h=Path('/home/dombarker/project-offloads/codex-cx-native-featparity-20261028')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true')
cases=[('library-default','crates/aspis-r1-cost-probe','aspis-r1-cost-probe',[]),('library-deployed','crates/aspis-r1-cost-probe','aspis-r1-cost-probe',['private-leaf-salts','optimized-terminal','program-build']),('statement-default','crates/aspis-statement','aspis-statement',[]),('core-default','crates/aspis-core','aspis-core',[]),('program-deployed','programs/r1-cost-probe','aspis-r1-cost-probe-program',['pool-adapter','private-leaf-salts']),('program-no-entrypoint','programs/r1-cost-probe','aspis-r1-cost-probe-program',['pool-adapter','private-leaf-salts','no-entrypoint'])]
import tomllib
for label,root,pkg,features in cases:
 pkg=tomllib.loads((w/root/'Cargo.toml').read_text())['package']['name']
 d=h/('NCS_graph_'+label);d.mkdir(exist_ok=True)
 manifest='[package]\nname="ncs-audit-root"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="empty.rs"\n[dependencies]\nncs-target={package='+json.dumps(pkg)+',path='+json.dumps(str(w/root))+',features='+json.dumps(features)+'}\n'
 (d/'Cargo.toml').write_text(manifest);(d/'empty.rs').write_text('')
 (d/'Cargo.lock').write_bytes((w/'Cargo.lock').read_bytes())
 cmd=['cargo','metadata','--offline','--format-version','1','--manifest-path',str(d/'Cargo.toml')]
 r=subprocess.run(cmd,cwd=d,env=env,capture_output=True,text=True)
 assert r.returncode==0,(label,r.stderr)
 j=json.loads(r.stdout);pk={p['id']:p for p in j['packages']}
 print(json.dumps(dict(label=label,command=cmd,manifest=manifest,root=j['resolve']['root'],nodes=[dict(id=n['id'],name=pk[n['id']]['name'],version=pk[n['id']]['version'],features=n['features'],deps=n['deps']) for n in j['resolve']['nodes']],lock_sha256=hashlib.sha256((w/'Cargo.lock').read_bytes()).hexdigest(),lock_changes=r.stderr)))
