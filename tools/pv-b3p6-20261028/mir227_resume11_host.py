"""Deployed optimized MIR and LLVM/symbol evidence, including inlined scopes.
Expected time: optimized compilation only; no proof generation or elimination.
"""
from run import H,run
from pathlib import Path
import json,hashlib,subprocess,sys
package=sys.argv[1];assert package in ['aspis-r1-cost-probe','aspis-statement','aspis-core']
f=json.loads((H/'llvm227-features-resume7.json').read_text())
for name,sha in f['source_freeze'].items():
 if name.startswith(('crates/','programs/')):assert hashlib.sha256((H/'source'/name).read_bytes()).hexdigest()==sha,name
p=H/'source/tools/pv-b3p6-20261028/v244/Cargo.toml'
cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','+1.94.1','rustc','--release','--locked','--offline','--manifest-path',str(p),'-p',package,'--lib','--jobs','4','--','--emit=mir,llvm-ir']
r=run('mir227-resume11-'+package,cmd,'optimized compilation to deployed MIR/LLVM including inlined scopes; no arithmetic gate',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
if r:raise SystemExit(r)
rows=[]
for ext in ['mir','ll','rlib']:
 for q in (H/'target/release/deps').glob(package.replace('-','_')+'-*.'+ext):rows.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
(H/('mir227-resume11-'+package+'.json')).write_text(json.dumps(dict(package=package,command=cmd,features_record='llvm227-features-resume7.json',source_revision=(H/'revision').read_text().strip(),artifacts=rows),indent=2)+'\n')
print(json.dumps(rows))
