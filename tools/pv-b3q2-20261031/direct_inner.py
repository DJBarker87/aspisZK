from pathlib import Path
import json,subprocess,hashlib,os
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');I=json.loads((H/'direct2-cone-extraction-input.json').read_text())
cmd=['cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',str(H/'direct-source/crates/aspis-r1-cost-probe/Cargo.toml'),'--features','prover,r1p-check,ct-host-prover']
r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=os.environ);(H/'direct-metadata.stderr').write_bytes(r.stderr);r.check_returncode();m=json.loads(r.stdout)
packages={p['id']:p for p in m['packages']};rows=[dict(name=packages[n['id']]['name'],version=packages[n['id']]['version'],source=packages[n['id']]['source'],features=n['features'])for n in m['resolve']['nodes']]
expected=I['inherited_wrapper_feature_parity']['deployed']['nodes'];needed=I['inherited_wrapper_feature_parity']['reached_crates'];bad=[]
for name in needed:
 a=[r for r in rows if r['name']==name];b=[r for r in expected if r['name']==name]
 if a!=b:bad.append(dict(name=name,direct=a,deployed=b))
x=dict(command=cmd,raw_sha256=hashlib.sha256(r.stdout).hexdigest(),nodes=rows,reached_crates=needed,mismatches=bad,profile=dict(name='release',opt_level=3,overflow_checks=False,debug_assertions=False,cfg_test=False))
(H/'direct-feature-association.json').write_text(json.dumps(x,indent=2)+'\n');assert not bad,bad
raise SystemExit(subprocess.run(I['command']).returncode)
