from run import H, run
from pathlib import Path
import sys,hashlib,json
kind=sys.argv[1]
P=H/'source/tools/pv-b3p6-20261028'
if kind=='kani133':
 (H/'tmp').mkdir(exist_ok=True)
 bounds=json.loads((H/'bounds133.json').read_text())
 cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--exact','--harness','proofs::shipped_equals_reference133_pointwise','--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','--cbmc-args','--symex-cache-dereferences','--reachability-slice-fb','--unwinding-assertions','--unwindset',','.join(k+':'+str(v['bound']) for k,v in bounds['loops'].items())]
 sys.exit(run('kani133-07',cmd,'optimized compilation then bounded control-flow/index/sort/dedup equality; no stubs, default unwind32 with per-loop bounds, universal auxiliary u8 index, forward/backward reachability slicing, dereference cache, no field multiplication',{'RUSTFLAGS':'--cfg kani','CARGO_PROFILE_DEV_OPT_LEVEL':'3','TMPDIR':str(H/'tmp')}))
if kind=='loops133':
 artifacts=list((H/'target/kani').glob('**/*shipped_equals_reference133.out'))
 assert len(artifacts)==1,artifacts
 cbmc='/home/dombarker/.kani/kani-0.67.0/bin/cbmc'
 cmd=['timeout','60','taskset','--cpu-list','0-3',cbmc,'--show-loops',str(artifacts[0])]
 sys.exit(run('loops133-01',cmd,'read-only loop inventory of the existing Kani goto artifact; no symbolic execution or SAT'))
if kind=='native133':
 cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','finite_native133','--','--exact','--nocapture']
 sys.exit(run('native133-01',cmd,'optimized native same-input differential; finite validation, not symbolic proof'))
if kind=='extract133':
 tools={'/home/dombarker/project-offloads/codex-pv-extract-20261027/charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'}
 for f,h in tools.items(): assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
 llbc=H/'PV_B3P_133.llbc'
 cmd=['timeout','180','taskset','--cpu-list','0-3',next(iter(tools)),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::reference133::active_rows','--include','pv_b3p6_reference::reference133::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 r=run('charon133-03',cmd,'optimized MIR extraction of owned literal reference; no arithmetic elimination',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')})
 if r:sys.exit(r)
 out=H/'generated133';out.mkdir()
 cmd=['timeout','180',list(tools)[1],'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_133','-dest',str(out),'-split-files','-emit-json',str(llbc)]
 sys.exit(run('aeneas133-01',cmd,'pinned fail-closed extraction with strict joins'))

if kind=='extract226':
 tools={'/home/dombarker/project-offloads/codex-pv-extract-20261027/charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'}
 for f,h in tools.items(): assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
 llbc=H/'PV_B3P_226_02.llbc'
 cmd=['timeout','180','taskset','--cpu-list','0-3',next(iter(tools)),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::reference226::public_bytes','--include','pv_b3p6_reference::reference226::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 r=run('charon226-02',cmd,'optimized MIR of owned public-input serializer with64-byte chunks; no arithmetic elimination',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')})
 if r:sys.exit(r)
 out=H/'generated226-02';out.mkdir()
 cmd=['timeout','180',list(tools)[1],'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_226','-dest',str(out),'-split-files','-emit-json',str(llbc)]
 sys.exit(run('aeneas226-02',cmd,'pinned fail-closed extraction of owned serializer; strict joins and abort-on-error unchanged'))
if kind=='native226':
 cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','native226::same_input_finite226','--','--exact','--nocapture']
 sys.exit(run('native226-01',cmd,'optimized same-input native serializer comparison, transfer/withdrawal and rejection cases; finite validation'))
