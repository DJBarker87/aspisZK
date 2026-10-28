from run import H, run
from pathlib import Path
import sys,hashlib,json
kind=sys.argv[1]
P=H/'source/tools/pv-b3p6-20261028'
def admission_label(base):
 label=base;i=0
 while (H/label).exists():
  assert not (H/label/'receipt/receipt.json').exists(), 'charged gate cannot be rerun unchanged: '+label
  i+=1;label=base+'-r'+str(i)
 return label
if kind in ('kani133','kmxcontrols','kani133_nofield','kmxcontrols_nofield','kani226v3'):
 patch=H/'source/evidence/pv-b3p6-20261028/KMX_copy_stubs.patch'
 stubs=P/'kmx/KMX_stubs.rs'
 patch_sha=hashlib.sha256(patch.read_bytes()).hexdigest()
 stubs_sha=hashlib.sha256(stubs.read_bytes()).hexdigest()
 definitions_sha=hashlib.sha256(stubs.read_text().split('#[cfg(kani)]',1)[0].encode()).hexdigest()
 assert definitions_sha=='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9'
 assert patch_sha=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert stubs_sha=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 (H/('copy-patch-preflight-'+kind+'.json')).write_text(json.dumps(dict(patch_sha256=patch_sha,stubs_sha256=stubs_sha,definitions_only_sha256=definitions_sha,source_revision=(H/'revision').read_text().strip(),business_function_stubs=False),indent=2)+'\n')
if kind in ('kani133','kani133_nofield'):
 (H/'tmp').mkdir(exist_ok=True)
 bounds=json.loads((H/'bounds133.json').read_text())
 cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--exact','--harness','proofs::shipped_equals_reference133_pointwise','--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing','--cbmc-args','--symex-cache-dereferences','--reachability-slice-fb','--unwinding-assertions','--unwindset',','.join(k+':'+str(v['bound']) for k,v in bounds['loops'].items())]
 if kind.endswith('_nofield'):cmd.append('--no-array-field-sensitivity')
 sys.exit(run(admission_label('kani133-kmx-nofield-09' if kind.endswith('_nofield') else 'kani133-kmx-08'),cmd,'optimized compilation then bounded control-flow/index/sort/dedup equality; exact lead KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67, default unwind1026 for replacement copy/realloc loops with per-loop bounds, universal auxiliary u8 index, forward/backward reachability slicing, dereference cache, no field multiplication',{'RUSTFLAGS':'--cfg kani','CARGO_PROFILE_DEV_OPT_LEVEL':'3','TMPDIR':str(H/'tmp')}))
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
if kind in ('extract226v3','aeneas226v3'):
 tools={'/home/dombarker/project-offloads/codex-pv-extract-20261027/charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'}
 for f,h in tools.items(): assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
 llbc=H/'PV_B3P_226_03.llbc'
 cmd=['timeout','180','taskset','--cpu-list','0-3',next(iter(tools)),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::reference226::public_bytes','--include','pv_b3p6_reference::reference226::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
 if kind=='extract226v3':
  sys.exit(run(admission_label('charon226-03'),cmd,'optimized MIR of direct owned M31 projection and8-byte subchunks',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')}))
 out=H/'generated226-03';out.mkdir(exist_ok=True)
 cmd=['timeout','180',list(tools)[1],'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_226V3','-dest',str(out),'-split-files','-emit-json',str(llbc)]
 sys.exit(run(admission_label('aeneas226-03'),cmd,'pinned fail-closed extraction of owned serializer; strict joins and abort-on-error unchanged'))
if kind=='native226':
 cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','native226::same_input_finite226','--','--exact','--nocapture']
 sys.exit(run('native226-01',cmd,'optimized same-input native serializer comparison, transfer/withdrawal and rejection cases; finite validation'))

if kind in ('kani226transfer','kani226withdrawal'):
 variant='transfer' if kind.endswith('transfer') else 'withdrawal'
 (H/'tmp').mkdir(exist_ok=True)
 cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--exact','--harness','native226::'+variant,'--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','--cbmc-args','--unwinding-assertions','--symex-cache-dereferences']
 sys.exit(run('kani226-'+variant+'-01',cmd,'optimized compilation then no-stub native complete-Result serializer check; universal auxiliary u16 index, unwind65, small-width arithmetic only',{'RUSTFLAGS':'--cfg kani','CARGO_PROFILE_DEV_OPT_LEVEL':'3','TMPDIR':str(H/'tmp')}))

if kind in ('kmxcontrols','kmxcontrols_nofield'):
 (H/'tmp').mkdir(exist_ok=True)
 cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--exact','--harness','KMX_stubs::KMX_checks::KMX_growth_wrong','--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
 if kind.endswith('_nofield'):cmd.append('--no-array-field-sensitivity')
 sys.exit(run(admission_label('kmx-growth-negative-nofield-02' if kind.endswith('_nofield') else 'kmx-growth-negative-01'),cmd,'exact lead KMX patch intended-negative growth control; optimized compilation, no business-function replacement; positive-control evidence is lead K008, not rerun here',{'RUSTFLAGS':'--cfg kani','CARGO_PROFILE_DEV_OPT_LEVEL':'3','TMPDIR':str(H/'tmp')}))
if kind=='fidelitynative226':
 cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','native226::emission_fixture226','--','--exact','--nocapture']
 sys.exit(run('native226-emission-01',cmd,'optimized same-input fixture output for emission/native comparison; finite validation, missing evidence artifact'))

if kind=='native226v3':
 cmd=['timeout','180','taskset','--cpu-list','0-3','cargo','test','--release','--manifest-path',str(P/'Cargo.toml'),'--lib','native226::','--','--nocapture','--test-threads=1']
 sys.exit(run(admission_label('native226-v3-01'),cmd,'optimized same-input native serializer checks and exact emission fixtures; finite validation of changed direct M31 projection and8-byte subchunks'))

if kind=='kani226v3':
 (H/'tmp').mkdir(exist_ok=True)
 cmd=['timeout','900','taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(P/'Cargo.toml'),'--lib','--harness','native226::both_variants','--solver','kissat','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions','--symex-cache-dereferences','--reachability-slice-fb','--no-array-field-sensitivity']
 sys.exit(run(admission_label('kani226-v3-both-01'),cmd,'optimized compilation then positive complete-Result serializer equality plus matched wrong-byte negative control for both variants in one invocation; universal auxiliary u16 index, unwind2049 covers reallocation byte prefixes; exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 with checked negative growth control under same array model; no business stubs or chained field arithmetic',{'RUSTFLAGS':'--cfg kani','CARGO_PROFILE_DEV_OPT_LEVEL':'3','TMPDIR':str(H/'tmp')}))
