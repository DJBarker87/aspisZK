"""Task-specific extraction of op223 in its unedited current-crate MIR context."""
from pathlib import Path
import subprocess,sys,json,shlex
root=Path(__file__).resolve().parents[2];stage=sys.argv[1]; variant=sys.argv[2] if len(sys.argv)>2 else 'op223-built'
assert stage in ('charon','aeneas')
base='/home/dombarker/project-offloads/codex-pv-cb3-20261026';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';pinned='/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools'
assert variant in ('op223-built','op249-staged')
name=stage+'-source-'+variant+'-resume'
entry='pv_cb3_source::compress_tagged_tuple' if variant=='op223-built' else 'pv_cb3_source::staged_reference::gamma'
include='pv_cb3_source::logup::*' if variant=='op223-built' else 'pv_cb3_source::staged_reference::*'
namespace='PV_CB3_Op223Built' if variant=='op223-built' else 'PV_CB3_Op249Staged';out=root/'evidence/pv-cb3-20261026'/name;out.mkdir(exist_ok=True)
def ssh(c):return subprocess.run(['ssh','dombarker@100.108.41.90',c],text=True,capture_output=True)
r=ssh(f'mkdir -p {base}/{name}; python3 {gate}/reservation.py {base}/{name}/admission-before.json > {base}/{name}/reservation.log 2>&1; cat {base}/{name}/reservation.log');(out/'admission-transport.log').write_text(r.stdout+r.stderr)
if not json.loads(r.stdout)['allowed']:print('REFUSED');sys.exit(78)
if stage=='charon':
 args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={base}/charon-target',pinned+'/charon','cargo','--preset','aeneas','--mir','built','--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry,'--include',include,'--dest-file',base+'/'+namespace+'.llbc','--','--manifest-path',base+'/source-proof/Cargo.toml','--release','--offline','--lib','--jobs','4']
else:
 args=['timeout','120',pinned+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',base+'/'+variant+'-generated','-split-files','-emit-json',base+'/'+namespace+'.llbc']
 assert ssh(f'mkdir -p {base}/{variant}-generated').returncode==0
receipt=dict(target=args,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_phase='optimized compilation / selected MIR extraction' if stage=='charon' else 'symbolic extraction of changed current-crate built MIR graph',print_axioms='N/A extraction',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
assert not (out/'target.json').exists();(out/'target.json').write_text(json.dumps(receipt,indent=2)+'\n')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',base+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',base+'/'+name+'/time.log',*args]
r=ssh(shlex.join(cmd)+f' > {base}/{name}/output.log 2>&1');(out/'transport.log').write_text(r.stdout+r.stderr)
subprocess.run([sys.executable,str(root/'tools/pv-cb3-20261026/collect_native.py'),name,'source-proof/lib.rs','source-proof/Cargo.toml',namespace+'.llbc',variant+'-generated/Funs.lean',variant+'-generated/Types.lean'],check=True)
p=out/'collected-receipt.json';r=json.loads(p.read_text());r.update(receipt);p.write_text(json.dumps(r,indent=2)+'\n');print(r['exit'])
