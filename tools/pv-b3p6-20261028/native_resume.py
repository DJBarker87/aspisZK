"""Only native finite-validation gates; no Kani invocation is available."""
from run import H,run
import sys
P=H/'source/tools/pv-b3p6-20261028'
label='native133-structural-resume'
i=0
while (H/label).exists():
 assert not (H/label/'receipt/receipt.json').exists()
 i+=1;label='native133-structural-resume-r'+str(i)
cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','finite_native133_structural','--','--exact','--nocapture']
sys.exit(run(label,cmd,'optimized Rust compilation then unit-input schedule/body/literal differential; finite validation, no arithmetic proof generation',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
