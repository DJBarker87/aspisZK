from pathlib import Path
import subprocess,json,os,hashlib
w=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026/src')
assert w.exists(),str(w)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true')
cases=[('library-default','crates/aspis-r1-cost-probe',[]),('library-deployed','crates/aspis-r1-cost-probe',['private-leaf-salts,optimized-terminal,program-build']),('statement-default','crates/aspis-statement',[]),('core-default','crates/aspis-core',[]),('program-deployed','programs/r1-cost-probe',['pool-adapter,private-leaf-salts']),('program-no-entrypoint','programs/r1-cost-probe',['pool-adapter,private-leaf-salts,no-entrypoint'])]
for label,root,features in cases:
 cmd=['cargo','metadata','--offline','--locked','--format-version','1','--manifest-path',str(w/root/'Cargo.toml')]
 if features:cmd+=['--features',features[0]]
 r=subprocess.run(cmd,cwd=w,env=env,capture_output=True,text=True)
 assert r.returncode==0,(label,r.stderr)
 j=json.loads(r.stdout);pk={p['id']:p for p in j['packages']}
 print(json.dumps(dict(label=label,command=cmd,root=j['resolve']['root'],nodes=[dict(id=n['id'],name=pk[n['id']]['name'],version=pk[n['id']]['version'],features=n['features'],deps=n['deps']) for n in j['resolve']['nodes']],lock_sha256=hashlib.sha256((w/'Cargo.lock').read_bytes()).hexdigest())))
