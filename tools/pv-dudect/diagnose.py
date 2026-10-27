#!/usr/bin/env python3
"""diagnostic, not a V374 measurement; normal capped scope, no window exemption."""
import pathlib,subprocess,sys,json,os,time,hashlib
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027')
stage=sys.argv[1]; O=B/('diagnosis-'+stage)
if len(sys.argv)==2:
 assert not pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json').exists(),'QUIET WINDOW HOLD'
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(B/('diagnosis-'+stage+'-admission.json'))])
 if r.returncode:sys.exit(r.returncode)
 assert json.loads((B/('diagnosis-'+stage+'-admission.json')).read_text())['allowed'] is True
 sys.exit(subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',__file__,stage,'worker']).returncode)
O.mkdir(exist_ok=False)
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(B/'harness-target'))
cmd={'build':['cargo','build','--manifest-path','tools/pv-dudect/Cargo.toml','--bin','diagnostic','--release','--offline','--locked','-j','4'],'controls':['taskset','-c','2',str(B/'harness-target/release/diagnostic')],'trace':['python3',str(B/'src/tools/pv-dudect/diagnostic_trace.py')],'analysis':['python3',str(B/'src/tools/pv-dudect/diagnostic_analyze.py'),str(B/'diagnosis-controls')]}[stage]
rec=dict(label='diagnostic, not a V374 measurement',target=cmd,source_revision='d03e24018cac5015c4b94f296df9f0c9154c6a6a plus tools-only diagnostic',print_axioms='N/A: no Lean',expected_work={'build':'optimized compilation/linking, cached dependencies','controls':'12 million interleaved expander calls and CSV I/O','trace':'static disassembly and artifact identity; no kernel calls','analysis':'offline Welch crop analysis'}[stage],limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']})
assert list(rec['limits'].values())==['6442450944','8589934592','0','64']
t=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=O if stage=='controls' else B/'src',env=env,stdout=so,stderr=se)
rec.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),swap_peak_bytes=int((cg/'memory.swap.peak').read_text()))
if stage=='controls':rec['binary_sha256']=hashlib.sha256((B/'harness-target/release/diagnostic').read_bytes()).hexdigest()
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(r.returncode)
