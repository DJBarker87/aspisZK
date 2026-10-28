from run import H,run
import sys
P=H/'source/tools/pv-b3p6-20261028/v241/Cargo.toml'
sys.exit(run('native224-helper-write-fidelity',['timeout','180','taskset','--cpu-list','0-3','cargo','+1.94.1','test','--release','--offline','--manifest-path',str(P),'--lib','fidelity224_helper_write','--','--exact','--nocapture'],'optimized compilation then one sparse changing write at helper row1023; all1024 ordered field words printed for emitted-source finite validation; not a proof',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
