"""Optimized finite replay then pinned extraction of the V228 owned candidate."""
from run import H,run
from pathlib import Path
import sys,hashlib
P=H/'source/tools/pv-b3p6-20261028/v228';kind=sys.argv[1]
array=kind.endswith('2');kind=kind.rstrip('2');suffix='-array' if array else ''
if kind=='native':
 sys.exit(run('native132-resume2'+suffix,['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--offline','--manifest-path',str(P/'Cargo.toml'),'--lib','native132_finite','--','--exact','--nocapture'],'expected time in optimized Rust compilation, then one same-input original/owned/reference comparison over3803 ordered output cells; finite validation',{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}))
charon=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');aeneas=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
assert hashlib.sha256(charon.read_bytes()).hexdigest()=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert hashlib.sha256(aeneas.read_bytes()).hexdigest()=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
llbc=H/('PV_B3P_132_resume2'+suffix+'.llbc')
if kind=='charon':
 cmd=['timeout','180','taskset','--cpu-list','0-3',str(charon),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::reference132::cells','--include','pv_b3p6_reference132::reference132::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 sys.exit(run('charon132-resume2'+suffix,cmd,'optimized compilation/MIR extraction of owned alias-free reference; original native link remains separate',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')}))
if kind=='aeneas':
 out=H/('generated132-resume2'+suffix);out.mkdir(exist_ok=True)
 sys.exit(run('aeneas132-resume2'+suffix,['timeout','180',str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_132','-dest',str(out),'-split-files','-emit-json',str(llbc)],'pinned fail-closed Aeneas extraction; strict joins, no bypass, no body edits'))
raise AssertionError(kind)
