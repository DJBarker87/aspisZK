"""Compare the actual rustc cfg arguments, not metadata's whole-workspace union.
No extracted cone is accepted if even one reached package's cfg is absent or
mismatched. Previous metadata rejection and its inputs remain immutable.
"""
from pathlib import Path
import json,subprocess,shlex,re
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');I=json.loads((H/'direct3-cone-extraction-input.json').read_text());cmd=I['command']+['--verbose']
r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(H/'direct3.stdout').write_bytes(r.stdout);(H/'direct3.stderr').write_bytes(r.stderr)
expected=I['inherited_wrapper_feature_parity']['deployed']['nodes'];needed=I['inherited_wrapper_feature_parity']['reached_crates'];found={name:[]for name in needed}
for line in (r.stdout+r.stderr).decode(errors='replace').splitlines():
 if 'Running `'not in line:continue
 raw=line.split('Running `',1)[1].rsplit('`',1)[0]
 try:args=shlex.split(raw)
 except ValueError:continue
 if '--crate-name'not in args:continue
 n=args[args.index('--crate-name')+1];name=next((n0 for n0 in needed if n0.replace('-','_')==n),None)
 if not name:continue
 cfg=[]
 for i,a in enumerate(args[:-1]):
  if a=='--cfg':
   m=re.fullmatch('feature="([^"]+)"',args[i+1])
   if m:cfg.append(m[1])
 row=dict(features=sorted(cfg),command_sha256=__import__('hashlib').sha256(raw.encode()).hexdigest())
 if row not in found[name]:found[name].append(row)
bad=[]
for name in needed:
 want=next(e['features']for e in expected if e['name']==name)
 if not found[name]or any(z['features']!=want for z in found[name]):bad.append(dict(name=name,actual=found[name],expected=want))
x=dict(command=cmd,compile_exit=r.returncode,actual_rustc_features=found,mismatches=bad,metadata_scope='N77117 captured the union across all workspace members; actual rustc command arguments are checked here instead.',no_cone_credit_without_match=True)
(H/'direct3-feature-association.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));r.check_returncode();assert not bad,bad
