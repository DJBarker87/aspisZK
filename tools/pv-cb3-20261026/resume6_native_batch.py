"""Plan and collect independent native stages, without overlapping scopes."""
from pathlib import Path
import subprocess,json,sys,datetime,time,shlex,ast,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026';label=sys.argv[1];variants=sys.argv[2:]
base='/home/dombarker/project-offloads/codex-pv-cb3-20261026';host='dombarker@100.108.41.90'
pinned='/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools'
tree=ast.parse((root/'tools/pv-cb3-20261026/resume6_extract.py').read_text())
entries=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='entries' for t in n.targets))
state=out/'RESUME6_ADMISSION_STATE.json';not_before=0
if state.exists():
    d=json.loads(state.read_text())
    if not d.get('allowed',False):not_before=datetime.datetime.fromisoformat(d['utc']).timestamp()+181
if not_before>time.time():print('LOCAL COOLDOWN',not_before-time.time());sys.exit(78)
plans=[]
for item in variants:
    stages=('charon','aeneas')
    if item.startswith('aeneas:'):variant=item.split(':',1)[1];stages=('aeneas',)
    else:variant=item
    entry,include,namespace=entries[variant];generated=base+'/'+variant+'-generated'
    for stage in stages:
        name=stage+'-source-'+variant+'-'+label;assert not (out/name).exists()
        if stage=='charon':
            args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={base}/charon-target',pinned+'/charon','cargo','--preset','aeneas','--mir',('optimized' if variant in ('op249-opt','op258-opt') else 'built'),'--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry,*sum((['--include',x] for x in include.split('+')),[]),'--dest-file',base+'/'+namespace+'.llbc','--','--manifest-path',base+'/source-proof/Cargo.toml','--release','--offline','--lib','--jobs','4']
        else:args=['timeout','120',pinned+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',generated,'-split-files','-emit-json',base+'/'+namespace+'.llbc']
        plans.append(dict(expected_phase=('optimized Rust compilation and selected MIR extraction' if stage=='charon' else 'symbolic Aeneas extraction of selected MIR'),name=name,stage=stage,variant=variant,namespace=namespace,target=args,generated=generated,mkdir=[generated] if stage=='aeneas' else []))
local=out/label;local.mkdir(exist_ok=True);assert not (local/'manifest.json').exists()
spec=dict(not_before=not_before,plans=plans,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(local/'manifest.json').write_text(json.dumps(spec,indent=2)+'\n')
remote=base+'/'+label
scanner='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
staging=subprocess.run(['ssh',host,'mkdir -p '+remote+'; python3 '+scanner+' '+remote+'/staging-admission.json > '+remote+'/staging-admission.log 2>&1; cat '+remote+'/staging-admission.log'],capture_output=True,text=True)
(local/'staging-admission.log').write_text(staging.stdout+staging.stderr)
d=json.loads(staging.stdout)
if not d['allowed']:
    state.write_text(json.dumps(dict(d,origin=label+' staging'))+'\n');sys.exit(78)

subprocess.run(['scp',str(local/'manifest.json'),str(root/'tools/pv-cb3-20261026/resume6_native_host.py'),host+':'+remote+'/'],check=True)
# Stage artifacts remain in the normal own host directory for the standing collector.
p=subprocess.run(['ssh',host,'python3 '+remote+'/resume6_native_host.py '+remote+'/manifest.json'],capture_output=True,text=True)
(local/'transport.log').write_text(p.stdout+p.stderr);print(p.stdout+p.stderr,flush=True)
for plan in plans:
    name=plan['name'];dest=out/name
    exists=subprocess.run(['ssh',host,'test -d '+remote+'/'+name]).returncode==0
    if not exists:continue
    dest.mkdir(exist_ok=True)
    subprocess.run(['scp','-r',host+':'+remote+'/'+name+'/.',str(dest)],check=True)
    # Collector expects base/name. This is an own-directory symlink, never shared infra.
    subprocess.run(['ssh',host,'test -e '+base+'/'+name+' || ln -s '+remote+'/'+name+' '+base+'/'+name],check=True)
    args=[sys.executable,str(root/'tools/pv-cb3-20261026/collect_native.py'),name,'source-proof/lib.rs','source-proof/Cargo.toml','source-proof/Cargo.lock','source-proof/resume6_digest.rs','source-proof/resume6_weights.rs','source-proof/resume6_owned_weights.rs','source-proof/resume6_tensor_reference.rs',plan['namespace']+'.llbc']
    subprocess.run(args,check=True)
    receipt=dest/'collected-receipt.json';d=json.loads(receipt.read_text());d.update({k:spec[k] for k in ('source_revision','limits')});d['target']=plan['target'];d['print_axioms']='N/A extraction';d['source_identity']='Frozen tracked shipped snapshot verified by RESUME6_SOURCE_IDENTITY.json; mutable harness input hashes retained per run.'
    receipt.write_text(json.dumps(d,indent=2)+'\n')
    bar=d.get('admissions',{}).get('admission-barrier.json',d.get('admissions',{}).get('admission-before.json',{}))
    if not bar.get('allowed',True):state.write_text(json.dumps(dict(utc=bar['utc'],allowed=False,origin=name))+'\n')
sys.exit(p.returncode)
