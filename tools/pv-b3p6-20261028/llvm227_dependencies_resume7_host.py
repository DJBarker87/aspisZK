"""Emit one reached shipped dependency in the same frozen native configuration."""
from run import H,run
from pathlib import Path
import json,subprocess,hashlib,sys
package=sys.argv[1];assert package in ['aspis-statement','aspis-core','blake2']
features=json.loads((H/'llvm227-features-resume7.json').read_text())
for name,sha in features['source_freeze'].items():
 if name.startswith(('crates/','programs/')):assert hashlib.sha256((H/'source'/name).read_bytes()).hexdigest()==sha,name
p=H/'source/tools/pv-b3p6-20261028/v244/Cargo.toml'
cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','+1.94.1','rustc','--release','--locked','--offline','--manifest-path',str(p),'-p',package,'--lib','--jobs','4','--','--emit=llvm-ir']
label='llvm227-resume7-'+package
while (H/label).exists():
 assert not (H/label/'receipt/receipt.json').exists(),'charged compiler cannot be rerun unchanged'
 label+='-r'
r=run(label,cmd,'optimized compilation of reached dependency to LLVM IR for formatting-path classification; no arithmetic gate',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
if r:raise SystemExit(r)
rows=[]
for q in (H/'target/release/deps').glob(package.replace('-','_')+'-*.ll'):
 rows.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
assert rows
(H/('llvm227-'+package+'-artifacts-resume7.json')).write_text(json.dumps(dict(package=package,features_record='llvm227-features-resume7.json',source_revision=(H/'revision').read_text().strip(),command=cmd,artifacts=rows),indent=2)+'\n')
print(json.dumps(rows))
