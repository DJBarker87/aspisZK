"""Task-specific extraction of op223 in its unedited current-crate MIR context."""
from pathlib import Path
import subprocess,sys,json,shlex,time,datetime
root=Path(__file__).resolve().parents[2];stage=sys.argv[1]; variant=sys.argv[2] if len(sys.argv)>2 else 'op223-built'
assert stage in ('charon','aeneas')
base='/home/dombarker/project-offloads/codex-pv-cb3-20261026';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';pinned='/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools'
assert variant in ('op223-built','op249-staged','op253-built','op34-hide-allocator','op34-method','op35-default','op258-reference','op253-source','op134-source','op79-source','op134-reference','op253-reference','op253-owned')
name=stage+'-source-'+variant+'-'+(sys.argv[3] if len(sys.argv)>3 else 'resume')
entries={
'op253-owned':('pv_cb3_source::resume6_weights::owned_raw','pv_cb3_source::resume6_weights::*','PV_CB3_Op253Owned'),
'op253-reference':('pv_cb3_source::resume6_weights::raw','pv_cb3_source::resume6_weights::*','PV_CB3_Op253Reference'),
'op134-reference':('pv_cb3_kani::resume6_mask_reference::masks','pv_cb3_kani::resume6_mask_reference::*','PV_CB3_Op134Reference'),
'op258-reference':('pv_cb3_kani::reference::all_slots_clear','pv_cb3_kani::reference::*','PV_CB3_Op258Reference'),
'op253-source':('aspis_r1_cost_probe::weights::Weights::raw','aspis_r1_cost_probe::weights::*','PV_CB3_Op253Source'),
'op134-source':('aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_copy_active_row_masks_v1','aspis_statement::pool_v1::pair_forest_hiding::*','PV_CB3_Op134Source'),
'op79-source':('aspis_core::r0::encoder::eval_message','aspis_core::r0::encoder::*+aspis_core::r0::basis::*','PV_CB3_Op79Source'),
'op223-built':('pv_cb3_source::compress_tagged_tuple','pv_cb3_source::logup::*','PV_CB3_Op223Built'),
'op249-staged':('pv_cb3_source::staged_reference::gamma','pv_cb3_source::staged_reference::*','PV_CB3_Op249Staged'),
'op253-built':('pv_cb3_source::current_raw','pv_cb3_source::current_weights::*','PV_CB3_Op253Built'),
'op34-hide-allocator':('pv_cb3_source::vec_empty','alloc::vec','PV_CB3_Op34HideAllocator'),
'op34-method':('pv_cb3_source::vec_empty','alloc::vec::_','PV_CB3_Op34Method'),
'op35-default':('pv_cb3_source::vec_default','alloc::vec::_::default','PV_CB3_Op35Default')}
entry,include,namespace=entries[variant]
out=root/'evidence/pv-cb3-20261026'
# Own-job cooldown only; shared admission infrastructure is unchanged.
state=out/'RESUME6_ADMISSION_STATE.json'
if state.exists():
 d=json.loads(state.read_text())
 when=datetime.datetime.fromisoformat(d['utc']).timestamp()
 left=when+180-time.time()
 if not d.get('allowed',False) and left>0:
  print(f'LOCAL COOLDOWN HOLD {left:.1f}s; no ID or compiler charged');sys.exit(78)

# Respect the three-minute cooldown without a blocking sleep or ID reuse.
for old in sorted(out.glob('38*-refusal.json'),reverse=True):
 record=json.loads(old.read_text())
 raw=record.get('output','')
 try:
  admission=json.loads(raw)
  when=datetime.datetime.fromisoformat(admission['utc']).timestamp()
 except (ValueError,KeyError,TypeError):continue
 remaining=when+180-time.time()
 if remaining>0:
  print(f'LOCAL COOLDOWN HOLD {remaining:.1f}s; no ID or compiler charged')
  sys.exit(78)
 break

out=root/'evidence/pv-cb3-20261026'/name;out.mkdir(exist_ok=True)

def ssh(c):return subprocess.run(['ssh','dombarker@100.108.41.90',c],text=True,capture_output=True)
r=ssh(f'mkdir -p {base}/{name}; python3 {gate}/reservation.py {base}/{name}/admission-before.json > {base}/{name}/reservation.log 2>&1; cat {base}/{name}/reservation.log');(out/'admission-transport.log').write_text(r.stdout+r.stderr)
if not json.loads(r.stdout)['allowed']:
 (root/'evidence/pv-cb3-20261026/RESUME6_ADMISSION_STATE.json').write_text(json.dumps(dict(json.loads(r.stdout),origin=name))+'\n')
 print('REFUSED');sys.exit(78)
if stage=='charon':
 args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={base}/charon-target',pinned+'/charon','cargo','--preset','aeneas',*(['--hide-allocator'] if variant.startswith('op34-') or variant=='op35-default' else []),'--mir','built','--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry,*sum((['--include',x] for x in include.split('+')),[]),*(['--opaque','alloc::vec::Vec','--opaque','alloc::vec::_::new','--opaque','alloc::vec::_::len'] if variant in ('op34-method','op35-default') else []),'--dest-file',base+'/'+namespace+'.llbc','--','--manifest-path',base+('/kani-proof/Cargo.toml' if variant in ('op258-reference','op134-reference') else '/source-proof/Cargo.toml'),'--release','--offline','--lib','--jobs','4']
else:
 args=['timeout','120',pinned+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',base+'/'+variant+'-generated','-split-files','-emit-json',base+'/'+namespace+'.llbc']
 assert ssh(f'mkdir -p {base}/{variant}-generated').returncode==0
receipt=dict(target=args,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_phase='optimized compilation / selected MIR extraction' if stage=='charon' else 'symbolic extraction of changed current-crate built MIR graph',print_axioms='N/A extraction',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
assert not (out/'target.json').exists();(out/'target.json').write_text(json.dumps(receipt,indent=2)+'\n')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',base+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',base+'/'+name+'/time.log',*args]
r=ssh(shlex.join(cmd)+f' > {base}/{name}/output.log 2>&1');(out/'transport.log').write_text(r.stdout+r.stderr)
subprocess.run([sys.executable,str(root/'tools/pv-cb3-20261026/collect_native.py'),name,'source-proof/lib.rs','source-proof/Cargo.toml','kani-proof/lib.rs','kani-proof/reference.rs','kani-proof/Cargo.toml',namespace+'.llbc',variant+'-generated/Funs.lean',variant+'-generated/Types.lean'],check=True)
p=out/'collected-receipt.json';r=json.loads(p.read_text());r.update(receipt);p.write_text(json.dumps(r,indent=2)+'\n')
bar=r.get('admissions',{}).get('admission-barrier.json',{})
if bar and not bar.get('allowed',True):
 (root/'evidence/pv-cb3-20261026/RESUME6_ADMISSION_STATE.json').write_text(json.dumps(dict(utc=bar['utc'],allowed=False,origin=name+' inside-scope refusal'))+'\n')
print(r['exit'])
