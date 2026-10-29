from run import H,run
from pathlib import Path
import json,hashlib,subprocess,sys
assert sys.argv[1]==(H/'revision').read_text().strip(),'revision label must equal the frozen owned source revision'
p=H/'source/tools/pv-b3p6-20261028/v244'
old=json.loads((H/'features227-resume4.json').read_text())
cmd=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--offline','--locked','--format-version','1','--manifest-path',str(p/'Cargo.toml')]
x=json.loads(subprocess.check_output(cmd,text=True));pkgs={r['id']:r for r in x['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in x['resolve']['nodes']]
assert sorted(nodes,key=lambda n:(n['name'],n['version']))==sorted(old['validation']['nodes'],key=lambda n:(n['name'],n['version']))
freeze=json.loads((H/'native227-parts-source-freeze.json').read_text());assert all(hashlib.sha256((H/'source'/name).read_bytes()).hexdigest()==sha for name,sha in freeze.items())
(H/'native227-parts-features.json').write_text(json.dumps(dict(revision=sys.argv[1],nodes=nodes,profile=old['profile'],lock_sha256=hashlib.sha256((p/'Cargo.lock').read_bytes()).hexdigest(),metadata_command=cmd,toolchain='1.94.1',source_freeze_count=len(freeze),evidence_class='finite validation only'),indent=2)+'\n')
sys.exit(run('native227-resume5-owned-parts',['timeout','300','taskset','--cpu-list','0-3','cargo','+1.94.1','run','--release','--locked','--offline','--manifest-path',str(p/'Cargo.toml'),'--bin','finite227-owned','--jobs','4'],'optimized compilation, then changed owned-reference64 complete Result comparisons against deployed native; finite validation only; original64 gate retained',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4','PV_REV':sys.argv[1]}))
