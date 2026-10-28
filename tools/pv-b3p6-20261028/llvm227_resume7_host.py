"""Emit op227's shipped crate LLVM under deployed features/profile/toolchain.
Time is expected in optimized compilation only, no proof generation/elimination.
"""
from run import H,run
from pathlib import Path
import json,subprocess,hashlib
p=H/'source/tools/pv-b3p6-20261028/v244'
old=json.loads((H/'features227-resume4.json').read_text())
cmd=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--offline','--locked','--format-version','1','--manifest-path',str(p/'Cargo.toml')]
x=json.loads(subprocess.check_output(cmd,text=True));pkgs={r['id']:r for r in x['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in x['resolve']['nodes']]
assert sorted(nodes,key=lambda n:(n['name'],n['version']))==sorted(old['validation']['nodes'],key=lambda n:(n['name'],n['version']))
freeze=json.loads((H/'native227-parts-source-freeze.json').read_text());assert all(hashlib.sha256((H/'source'/name).read_bytes()).hexdigest()==sha for name,sha in freeze.items())
(H/'llvm227-features-resume7.json').write_text(json.dumps(dict(nodes=nodes,profile=old['profile'],metadata_command=cmd,toolchain='1.94.1',source_freeze=freeze,lock_sha256=hashlib.sha256((p/'Cargo.lock').read_bytes()).hexdigest(),boundary='targeted deployed-configuration LLVM; not a rebuild of deployed executable'),indent=2)+'\n')
cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','+1.94.1','rustc','--release','--locked','--offline','--manifest-path',str(p/'Cargo.toml'),'-p','aspis-r1-cost-probe','--lib','--jobs','4','--','--emit=llvm-ir']
r=run('llvm227-resume7-01',cmd,'optimized compilation of unchanged shipped crate to LLVM IR for formatting-path classification; no arithmetic gate',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
if r:raise SystemExit(r)
rows=[]
for q in (H/'target/release/deps').glob('aspis_r1_cost_probe-*.ll'):
 rows.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
assert rows
(H/'llvm227-artifacts-resume7.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows))
