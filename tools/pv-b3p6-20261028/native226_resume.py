"""Optimized finite native serializer differential; never invokes Kani."""
from run import H,run
import sys,json,hashlib
P=H/'source/tools/pv-b3p6-20261028'
expected=json.loads((H/'native226-resume-source-pins.json').read_text())
for rel,sha in expected.items():
 q=H/'source'/rel
 assert hashlib.sha256(q.read_bytes()).hexdigest()==sha,rel
base='native226-structural-resume';label=base;i=0
while (H/label).exists():
 assert not (H/label/'receipt/receipt.json').exists()
 i+=1;label=base+'-r'+str(i)
cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','native226::structural_source226','--','--exact','--nocapture']
sys.exit(run(label,cmd,'optimized compilation then 2884 same-input native/owned/reference complete-Result serializer comparisons; finite validation; no proof generation or arithmetic elimination',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
