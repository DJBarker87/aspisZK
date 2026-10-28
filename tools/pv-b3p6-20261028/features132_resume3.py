"""Read-only deployed feature graph and reached-body identity evidence for V228."""
from pathlib import Path
import subprocess,json,hashlib,re
from run import H
root=H/'source';out=H/'features132-resume3.json'
def graph(manifest,features=()):
 cmd=['cargo','+1.94.1','metadata','--offline','--format-version','1','--manifest-path',str(manifest)]
 if features:cmd+=['--features',','.join(features)]
 r=subprocess.run(cmd,cwd=root,text=True,capture_output=True)
 assert r.returncode==0,(cmd,r.stderr)
 data=json.loads(r.stdout);pkgs={p['id']:p for p in data['packages']}
 nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],features=n['features']) for n in data['resolve']['nodes']]
 return dict(command=cmd,nodes=nodes,raw_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),stderr=r.stderr)
a=graph(root/'tools/r1-cost-probe/Cargo.toml',['r1p-check','aspis-r1-cost-probe/ct-host-prover'])
b=graph(root/'tools/pv-b3p6-20261028/v228/Cargo.toml')
reached=['aspis-statement','aspis-prover','aspis-core']
differences=[]
for name in reached:
 x=next(n for n in a['nodes'] if n['name']==name);y=next(n for n in b['nodes'] if n['name']==name)
 if x['features']!=y['features']:differences.append(dict(crate=name,deployed=x['features'],validation=y['features']))
# Exact body audit is recorded by structural132.py; any feature differences are
# permitted only for bodies with no cfg/cfg!/debug_assert feature selection.
record=dict(deployed=a,validation=b,reached_crates=reached,feature_differences=differences,
 profile=dict(name='release',opt_level=3,overflow_checks=False,debug_assertions=False),
 toolchain=subprocess.check_output(['rustup','run','1.94.1','rustc','--version'],text=True).strip(),
 extraction_body_identity='reference132.rs contains no feature/cfg/debug-assert selection; exact source pinned by structural132.py',
 no_kani=True)
out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(dict(feature_differences=differences,toolchain=record['toolchain'],crates_recorded=[len(a['nodes']),len(b['nodes'])])))
