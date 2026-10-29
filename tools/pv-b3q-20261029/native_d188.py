from pathlib import Path
import json,hashlib,subprocess,sys
from run import H,run
B=H.parent/'codex-pv-b3p6-20261028';P=H/'d188';old=json.loads((B/'features227-resume4.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads(subprocess.check_output(['cargo','+1.94.1','metadata','--offline','--locked','--format-version','1','--manifest-path',str(P/'Cargo.toml')],text=True));pkgs={p['id']:p for p in meta['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in meta['resolve']['nodes']]
# Library target removal does not change package dependency feature resolution.
assert sorted(nodes,key=lambda n:(n['name'],n['version']))==sorted(old['validation']['nodes'],key=lambda n:(n['name'],n['version']))
freeze=json.loads((B/'native227-composition-source-freeze.json').read_text());assert all(sha(B/'source'/p)==h for p,h in freeze.items())
x=dict(toolchain=subprocess.check_output(['rustc','+1.94.1','-vV'],text=True),nodes=nodes,profile=old['profile'],input_hashes={str(p.relative_to(H)):sha(p)for p in P.iterdir()if p.is_file()},inherited_source_freeze=freeze,evidence_class='finite validation of owned native source versus exact emitted model; not complete changed-function native association')
(H/'native-d188-inputs.json').write_text(json.dumps(x,indent=2)+'\n')
cmd=['timeout','600','taskset','--cpu-list','0-3','cargo','+1.94.1','run','--release','--locked','--offline','--manifest-path',str(P/'Cargo.toml'),'--bin','d188-b3q','--jobs','4']
r=run('native-d188',cmd,'optimized compilation followed by ten named changed-output helper observations; no elimination or proof generation',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
p=H/'target/release/d188-b3q'
if p.exists():(H/'native-d188-binary.json').write_text(json.dumps(dict(sha256=sha(p),bytes=p.stat().st_size),indent=2)+'\n')
raise SystemExit(r)
