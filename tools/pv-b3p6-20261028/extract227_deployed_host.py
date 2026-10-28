"""Attempt the unchanged pinned extractor only with required deployed sysroot.
A compiler/sysroot rejection is retained; no nightly fallback or tool rebuild.
"""
from run import H,run
from pathlib import Path
import hashlib,json,subprocess,sys
p=H/'source/tools/pv-b3p6-20261028/v244'
charon=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
assert hashlib.sha256(charon.read_bytes()).hexdigest()=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
x=json.loads((H/'features227-resume4.json').read_text());assert x['feature_differences']==[]
sysroot=subprocess.check_output(['rustup','run','1.94.1','rustc','--print','sysroot'],text=True).strip()
cmd=['timeout','300','taskset','--cpu-list','0-3',str(charon),'cargo','--preset','aeneas','--mir','optimized','--sysroot',sysroot,'--start-from','crate::host_terminal::r0::Public::terminal_qm31','--include','pv_b3p6_reference227::host_terminal::*','--include','pv_b3p6_reference227::host_copy_terminal::*','--include','pv_b3p6_reference227::host_terminal_field::*','--include','aspis_core::field::*','--dest-file',str(H/'PV_B3P_227_resume4.llbc'),'--','--manifest-path',str(p/'Cargo.toml'),'--release','--locked','--offline','--lib','--jobs','4']
sys.exit(run('charon227-deployed-resume4',cmd,'compatibility/extraction gate: unchanged pinned Charon, explicitly required rustc1.94.1 sysroot and matching std sources, optimized MIR and exact deployed features; no fallback to the pinned nightly sysroot',{'RUSTUP_TOOLCHAIN':'1.94.1','CARGO_TARGET_DIR':str(H/'charon-target')}))
