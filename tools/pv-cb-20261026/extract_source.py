"""Reproducible focused source extraction, using the standing resource gate."""
import json,shlex,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
op,entry,include=sys.argv[1:4]
project=sys.argv[6] if len(sys.argv)>6 else ('source-proof' if int(op)>=71 else 'proof')
base='/home/dombarker/project-offloads/codex-pv-cb-20261026'
scanner='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
def ssh(cmd):return subprocess.run(['ssh','dombarker@100.108.41.90',cmd],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
for stage in (sys.argv[5].split(',') if len(sys.argv)>5 else ['charon','aeneas']):
 name=f'{stage}-source-op{op}-{sys.argv[4] if len(sys.argv)>4 else "001"}';dest=f'{base}/{name}';local=root/'evidence/pv-cb-20261026'/name
 local.mkdir(exist_ok=True)
 assert not (local/'target.json').exists()
 out=ssh(f'mkdir -p {dest}; python3 {scanner} {dest}/admission-before.json > {dest}/reservation.log 2>&1')
 (local/'reservation-transport.log').write_text(out.stdout)
 if out.returncode:print(name,'reservation refused',out.returncode);sys.exit(out.returncode)
 if stage=='charon' and project in ['proof','source-proof','step-proof']:
  subprocess.run(['scp',str(root/'tools/pv-cb-20261026'/project/'lib.rs'),'dombarker@100.108.41.90:'+base+'/'+project+'/lib.rs'],check=True)
 if stage=='charon':
  args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={base}/charon-target',charon,'cargo','--preset','aeneas','--mir','built',*(['--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract'] if project in ['source-proof','proof','step-proof'] else []),'--sysroot','default','--start-from',entry]
  if include:
   for pattern in include.split('+'):args+=['--include',pattern]
  args+=['--dest-file',f'{base}/PV_CB_ShippedOp{op}.llbc','--','--manifest-path',f'{base}/{project}/Cargo.toml','--release','--offline','--lib','--jobs','4',*(['--features','ct-host-prover' if project.endswith('aspis-r1-cost-probe') else 'r0'] if project.startswith('source/crates/') else [])]
 else:
  assert ssh(f'mkdir -p {base}/shipped-op{op}-generated').returncode==0
  args=['timeout','120',aeneas,'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_CB_ShippedOp{op}','-dest',f'{base}/shipped-op{op}-generated','-split-files','-emit-json',f'{base}/PV_CB_ShippedOp{op}.llbc']
 target=dict(target=args,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),print_axioms='N/A extraction; corresponding Lean proof receipt required')
 (local/'target.json').write_text(json.dumps(target,indent=2)+'\n')
 cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',f'{dest}/time.log',*args]
 out=ssh(f'{shlex.join(cmd)} > {dest}/output.log 2>&1')
 (local/'transport.log').write_text(out.stdout)
 subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/collect_native.py'),name,f'PV_CB_ShippedOp{op}.llbc',f'shipped-op{op}-generated/Funs.lean',f'shipped-op{op}-generated/Types.lean',f'shipped-op{op}-generated/translation.json','source-proof/lib.rs','source-proof/Cargo.toml','source-proof/Cargo.lock','source/crates/aspis-core/src/field.rs','source/crates/aspis-core/src/field/ct.rs','source/crates/aspis-core/src/state_only_hiding.rs','source/crates/aspis-core/src/state_only_prefix.rs'],check=True)
 receipt=json.loads((local/'collected-receipt.json').read_text());receipt.update(target)
 (local/'collected-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(name,'exit',receipt['exit'])
 if out.returncode:sys.exit(out.returncode)

 if stage=='aeneas' and not out.returncode:
  raw=ssh(f'cat {base}/shipped-op{op}-generated/translation.json')
  meta=json.loads(raw.stdout);tail='::'+entry.split('::')[-1]
  matches=[f.get('rust_name') for kind in ['functions','globals'] for f in meta.get(kind,[]) if f.get('rust_name','').endswith(tail)]
  check=dict(requested_root=entry,matching_emitted_roots=matches,root_emitted=bool(matches),function_count=len(meta.get('functions',[])),global_count=len(meta.get('globals',[])))
  (local/'translation-validation.json').write_text(json.dumps(check,indent=2)+'\n')
  if not matches:
   print(name,'no matching extracted root; zero exit is not a source law')
   sys.exit(79)
