from run import H,run
from pathlib import Path
import sys
P=H/'source/tools/pv-b3p6-20261028/v241/Cargo.toml'
sys.exit(run('native224-prefix-side-fidelity',['timeout','180','taskset','--cpu-list','0-3','cargo','+1.94.1','test','--release','--offline','--manifest-path',str(P),'--lib','fidelity224_prefix_side','--','--exact','--nocapture'],'optimized compilation then four sparse native side writes at row1023, including zero-weight slot overwrite; emitted-side finite comparison will use this exact word vector, not proof credit',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
