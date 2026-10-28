"""V241 owned helper-continuation extraction; not a complete op224 closure."""
from run import H,run as run_once
from pathlib import Path
import hashlib,sys
def run(label,*args,**kwargs):
 base=label;retry=0
 while (H/label).exists():
  assert not (H/label/'receipt/receipt.json').exists(), 'unchanged charged gate cannot be retried'
  retry+=1;label=base+'-r'+str(retry)
 return run_once(label,*args,**kwargs)
kind=sys.argv[1];P=H/'source/tools/pv-b3p6-20261028/v241'
charon=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
aeneas=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
assert hashlib.sha256(charon.read_bytes()).hexdigest()=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert hashlib.sha256(aeneas.read_bytes()).hexdigest()=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
llbc=H/'PV_B3P_224_resume3_owned_read.llbc'
if kind=='native':
 sys.exit(run('native224-resume3-owned-read',['timeout','300','taskset','--cpu-list','0-3','cargo','+1.94.1','test','--release','--offline','--manifest-path',str(P/'Cargo.toml'),'--lib','finite224_rows','--','--exact','--nocapture'],'time expected in optimized compilation, then 80 same-input 1024-row continuation comparisons including zero-weight and active-pole branches; finite validation only',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
if kind=='charon':
 cmd=['timeout','300','taskset','--cpu-list','0-3',str(charon),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::reference224::from_rows','--include','pv_b3p6_reference224::reference224::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 sys.exit(run('charon224-resume3-owned-read',cmd,'optimized MIR of owned helper continuation with deployed ct-host-prover field arithmetic; no elimination/proof generation',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')}))
if kind=='aeneas':
 out=H/'generated224-resume3-owned-read';out.mkdir(exist_ok=True)
 sys.exit(run('aeneas224-resume3-owned-read',['timeout','300',str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_224','-dest',str(out),'-split-files','-emit-json',str(llbc)],'pinned fail-closed Aeneas helper-continuation extraction; strict joins, no bypass, no body edits'))
raise AssertionError(kind)
