"""Record post-macro text using the pinned extractor's rustc and configuration.
Compilation/expansion evidence only; these are not native arithmetic checks.
"""
from run import H, run
from pathlib import Path
import hashlib, json, subprocess, sys

package = sys.argv[1]
assert package in ['pv-b3p6-reference227', 'aspis-statement', 'aspis-core', 'aspis-r1-cost-probe']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze = json.loads((H/'native227-composition-source-freeze.json').read_text())
assert all(sha(H/'source'/n) == s for n,s in freeze.items())
charon = Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
assert sha(charon) == 'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
toolchain = subprocess.check_output([str(charon),'toolchain-version'],text=True).strip()
p = H/'source/tools/pv-b3p6-20261028/v244/Cargo.toml'
metadata_cmd = ['/home/dombarker/.cargo/bin/cargo','+'+toolchain,'metadata','--offline','--locked','--format-version','1','--manifest-path',str(p)]
metadata = json.loads(subprocess.check_output(metadata_cmd,text=True))
pkgs = {r['id']:r for r in metadata['packages']}
nodes = [dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features']) for n in metadata['resolve']['nodes']]
prior = json.loads((H/'features227-resume4.json').read_text())
assert sorted(nodes,key=lambda n:(n['name'],n['version'])) == sorted(prior['validation']['nodes'],key=lambda n:(n['name'],n['version']))
cmd = ['timeout','900','taskset','--cpu-list','0-3','cargo','+'+toolchain,'rustc','--release','--locked','--offline','--manifest-path',str(p),'-p',package,'--lib','--jobs','4','--','-Zunpretty=expanded']
label = 'expanded227-resume12-'+package
result = run(label,cmd,'optimized-profile compilation and post-macro source emission; no proof generation or elimination',{'CARGO_TARGET_DIR':str(H/'charon-target')})
if result: raise SystemExit(result)
out = H/label/'receipt/stdout.log'
record = dict(package=package,command=cmd,toolchain=toolchain,charon_sha256=sha(charon),profile=prior['profile'],nodes=nodes,source_freeze_sha256=sha(H/'native227-composition-source-freeze.json'),expanded_path=str(out),expanded_sha256=sha(out),bytes=out.stat().st_size,print_axioms='N/A: source expansion')
(H/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(package=package,sha256=sha(out),bytes=out.stat().st_size)))
