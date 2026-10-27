"""Serial, capped, receipt-producing extraction runner; never modifies shared tools."""
from pathlib import Path
import subprocess,shlex,json,sys,hashlib,re,datetime
ROOT=Path(__file__).resolve().parents[2]; OUT=ROOT/'evidence/pv-op134-20261027'
BASE='/home/dombarker/project-offloads/codex-pv-op134-20261027'
HOST='dombarker@100.108.41.90'
GATE='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
PIN='/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools'
def ssh(cmd):return subprocess.run(['ssh',HOST,cmd],text=True,capture_output=True)
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
mode,name,*extra=sys.argv[1:]; dest=BASE+'/'+name; out=OUT/name;out.mkdir(exist_ok=True)
assert not (out/'receipt.json').exists()
state=OUT/'admission-state.json'
if state.exists():
 s=json.loads(state.read_text()); left=s['retry_after']-__import__('time').time()
 if left>0:print('COOLDOWN',left);sys.exit(78)
# Pin actual working inputs for every new host run.
source_snapshots={}
if mode!='setup':
 for f in ['lib.rs','Cargo.toml','Cargo.lock','reference.rs','hiding-with-harness.rs','reference_encoder.rs','reference_multilinear.rs','constraints-fragments.rs','oracle-fragments.rs']:
  snap=ssh('cat '+BASE+'/source-proof/'+f)
  if snap.returncode==0:
   data=snap.stdout.encode();(out/(f+'.txt')).write_bytes(data)
   source_snapshots[f]=dict(sha256=hashlib.sha256(data).hexdigest(),size=len(data))
quiet="import pathlib,json,time,datetime; p=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json'); until=float(json.loads(p.read_text()).get('until',0)) if p.exists() else 0; held=time.time()<until; print(json.dumps(dict(allowed=False,reason='QUIET WINDOW HOLD',until=until,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))) if held else None; raise SystemExit(78 if held else 0)"
r=ssh(f'mkdir -p {dest}; python3 -c {shlex.quote(quiet)} > {dest}/reservation.log 2>&1 && python3 {GATE}/reservation.py {dest}/admission-before.json >> {dest}/reservation.log 2>&1; status=$?; cat {dest}/reservation.log; exit $status')
(out/'reservation.log').write_text(r.stdout+r.stderr)
if r.returncode:
 with (OUT/'ADMISSION-REFUSALS.jsonl').open('a') as journal:
  journal.write(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),mode=mode,name=name,charged=False,exit=r.returncode,reason=r.stdout+r.stderr))+'\n')
 save(state,dict(retry_after=__import__('time').time()+(30 if 'FileNotFoundError' in r.stdout else 180),reason=r.stdout+r.stderr));sys.exit(78)
if mode=='setup':
 assert ssh(f'mkdir -p {BASE}/source-proof').returncode==0
 for local,remote in [('source-Cargo.toml','Cargo.toml'),('source-lib.rs','lib.rs'),('reference.rs','reference.rs'),('hiding-with-harness.rs','hiding-with-harness.rs'),('constraints-fragments.rs','constraints-fragments.rs'),('oracle-fragments.rs','oracle-fragments.rs'),('reference_encoder.rs','reference_encoder.rs'),('reference_multilinear.rs','reference_multilinear.rs')]:subprocess.run(['scp',str(ROOT/'tools/pv-cbmid-20261027'/local),f'{HOST}:{BASE}/source-proof/{remote}'],check=True)
 print('setup uploaded after admission');sys.exit()
op=extra[0]; namespace='PV_Op134_Op'+op+'Raw'
entries={'79owned':'reference_encoder::eval_message_owned','132fill':'reference::fill_cells','133fill':'reference::fill_rows','222ref':'reference_multilinear::evaluate','79ref':'reference_encoder::eval_message_indexed','132ref':'reference::cells','auxref':'reference::aux_used','134ref':'reference::masks','133ref':'reference::rows','222':'constraints_v4::multilinear_evaluate_qm31','224':'pool_v1::oracle::build_pool_v1_pair_forest_copy_helper_v1','132':'pool_v1::hiding::pool_v1_pair_forest_relation_free_mask_cells_v1','133':'pool_v1::hiding::pool_v1_pair_forest_copy_active_rows_v1','134':'pool_v1::hiding::pool_v1_pair_forest_copy_active_row_masks_v1','79':'r0::encoder::eval_message'}
if mode=='charon':
 entry='pv_cbm_source::'+entries[op]
 include=('pv_cbm_source::reference_multilinear::*' if op=='222ref' else 'pv_cbm_source::reference_encoder::*' if op in ('79ref','79owned') else 'pv_cbm_source::constraints_v4::*' if op=='222' else 'pv_cbm_source::pool_v1::oracle::*' if op=='224' else 'pv_cbm_source::reference::*' if (op.endswith('ref') or op.endswith('fill')) else 'pv_cbm_source::pool_v1::hiding::*') if op!='79' else 'pv_cbm_source::r0::encoder::eval_message'
 args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={BASE}/charon-target',PIN+'/charon','cargo','--preset','aeneas','--mir','built','--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry,'--include',include,'--dest-file',BASE+'/'+namespace+'.llbc','--','--manifest-path',BASE+'/source-proof/Cargo.toml','--release','--offline','--lib','--jobs','4']
 if op in ('79ref','79owned'):
  at=args.index('--dest-file');args[at:at]=['--include','pv_cbm_source::r0::basis::*']
elif mode=='aeneas':
 assert ssh(f'mkdir -p {BASE}/op{op}-generated').returncode==0
 args=['timeout','120',PIN+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',BASE+'/op'+op+'-generated','-split-files','-emit-json',BASE+'/'+namespace+'.llbc']
elif mode=='kani':
 tally=json.loads((OUT/'TALLY.json').read_text());assert len(tally['kani_charged'])<4
 tally['kani_charged'].append(name);save(OUT/'TALLY.json',tally)
 timeout_s=int(extra[1]) if len(extra)>1 else 180
 assert timeout_s in (180,900)
 if timeout_s==900:
  assert op=='checks::masks_complete' and name=='kani-masks-900-001'
  old=json.loads((OUT/'kani-masks-001/receipt.json').read_text());assert old['exit']==124
 args=['timeout',str(timeout_s),'taskset','--cpu-list','0-3','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3','CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=false','CARGO_PROFILE_DEV_OVERFLOW_CHECKS=false','RUSTFLAGS=--cfg kani',f'CARGO_TARGET_DIR={BASE}/kani-target','cargo','kani','--manifest-path',BASE+'/source-proof/Cargo.toml','--lib','--exact','--harness',op,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','4','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
else:raise ValueError(mode)
receipt=dict(target=args,source_snapshots=source_snapshots,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),expected_phase='optimized compile and selected built MIR extraction' if mode=='charon' else f'optimized compilation; expected dominant step is CBMC symbolic checking of {op}, with exact source bounds and no stubs' if mode=='kani' else 'Aeneas translation',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),print_axioms='N/A extraction; no Lean theorem yet')
save(out/'target.json',receipt)
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',GATE+'/barrier.py',dest+'/admission-barrier.json','/usr/bin/time','-v','-o',dest+'/time.log',*args]
r=ssh(shlex.join(cmd)+f' > {dest}/output.log 2>&1');receipt['exit']=r.returncode
if mode=='kani':
 receipt['timeout_seconds']=timeout_s
 receipt['ruling']='pv-common.txt ruling (i), 2026-10-27 03:15 UTC' if timeout_s==900 else 'initial 180s gate'
 if r.returncode==124:receipt['rss_caveat']='GNU time maximum is retained as observed; killed-descendant aggregate RSS is unknown, not the GNU time parent maximum.'
for f in ['output.log','time.log','admission-before.json','admission-barrier.json']:
 t=ssh('cat '+dest+'/'+f);(out/f).write_text(t.stdout+t.stderr)
try:barrier=json.loads((out/'admission-barrier.json').read_text())
except (ValueError,FileNotFoundError):barrier={}
if barrier.get('allowed') is False:
 receipt['charged']=False
 receipt['compiler_started']=False
 if mode=='kani':
  tally=json.loads((OUT/'TALLY.json').read_text());tally['kani_charged'].remove(name);save(OUT/'TALLY.json',tally)
 save(state,dict(retry_after=__import__('time').time()+180,reason='inside-scope admission refusal: '+json.dumps({k:v for k,v in barrier.items() if k not in ('cgroups','uncapped_background')})))
t=(out/'time.log').read_text()
receipt['wall']=re.findall(r'Elapsed \(wall clock\) time.*: (.*)',t)
receipt['peak_rss_kib']=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',t)
receipt['swap']=re.findall(r'Swaps: (\d+)',t)
for file in ([] if mode=='kani' else [namespace+'.llbc'] if mode=='charon' else ['op'+op+'-generated/Funs.lean','op'+op+'-generated/Types.lean','op'+op+'-generated/ExternalFuns.lean','op'+op+'-generated/ExternalTypes.lean','op'+op+'-generated/translation.json']):
 t=ssh('cat '+shlex.quote(BASE+'/'+file))
 if t.returncode==0:
  data=t.stdout.encode();receipt.setdefault('artifacts',{})[file]=dict(sha256=hashlib.sha256(data).hexdigest(),size=len(data))
  if len(data)<2000000:(out/Path(file).name).write_bytes(data)
save(out/'receipt.json',receipt)
print(mode,name,'exit',r.returncode);print((out/'output.log').read_text()[-1800:]);sys.exit(r.returncode)
