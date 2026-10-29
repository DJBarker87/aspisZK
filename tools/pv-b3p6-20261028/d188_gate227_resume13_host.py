"""Inner capped native comparison against frozen Lean VM observations."""
from pathlib import Path
import json,subprocess,sys
from run import H
mode=sys.argv[1];expected=json.loads((H/'d18813-expected.json').read_text())
p=H/'source/tools/pv-b3p6-20261028/v244-d18813'
cmd=['cargo','+1.94.1','run','--release','--offline','--locked','--manifest-path',str(p/'Cargo.toml'),'--bin','d18813','--jobs','4']
if mode=='negative':cmd+=['--','--negative']
r=subprocess.run(cmd,text=True,capture_output=True);print(r.stderr[-3000:],file=sys.stderr);print(r.stdout);assert r.returncode==0,('native compilation/execution',r.returncode)
actual=[json.loads(s)for s in r.stdout.splitlines()if s.startswith('{')];assert len(actual)==len(expected)==16
key=lambda r:(r['function'],r['seed'])
assert sorted(actual,key=key)==sorted(expected,key=key),'Lean/native observation mismatch (negative mode intentionally perturbs one stored limb)'
print(json.dumps(dict(equal_observations=16,changed_write_cases=8,nonzero_result_cases=8,universal_claim=False)))
