"""Collect one small local Std-only lake env lean check; no compilation is launched."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parents[2];p=root/'evidence/pv-cb3-20261026'
a,module,code=sys.argv[1:4]
out=(p/f'out-{a}-local.log').read_text();time=(p/f'time-{a}-local.log').read_text()
assert int(code) != 0 or 'error:' not in out, 'Cannot record exit 0 for an error-bearing local log'
source=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean'
stdlib=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean/Std.olean')
imports={'Std':hashlib.sha256(stdlib.read_bytes()).hexdigest()}
r=dict(attempt=int(a),module=module,environment='local Std-only Lean4.32.0, focused-job exception; no host scope',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),dependency_object_hashes=imports,deps_fingerprint=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest(),exit=int(code),wall=re.search(r'([0-9.]+) real',time)[1]+' seconds',peak_rss_kib=int(re.search(r'(\d+)\s+maximum resident set size',time)[1])//1024,swap=int(re.search(r'(\d+)\s+swaps',time)[1]),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S),limits=dict(lean_M=7000,local_focused=True),target=['lake','env','lean','-M7000',str(source)])
(p/f'{a}.json').write_text(json.dumps(r,indent=2)+'\n');print(a,r['exit'],r['wall'],r['peak_rss_kib'],'KiB')
