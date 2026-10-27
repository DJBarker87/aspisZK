"""Serial, capped, receipt-producing extraction runner; never modifies shared tools."""
from pathlib import Path
import subprocess,shlex,json,sys,hashlib,re,datetime
ROOT=Path(__file__).resolve().parents[2]; OUT=ROOT/'evidence/pv-cbmid-20261027'
BASE='/home/dombarker/project-offloads/codex-pv-cbmid-20261027'
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
r=ssh(f'mkdir -p {dest}; python3 {GATE}/reservation.py {dest}/admission-before.json > {dest}/reservation.log 2>&1; status=$?; cat {dest}/reservation.log; exit $status')
(out/'reservation.log').write_text(r.stdout+r.stderr)
if r.returncode:
 save(state,dict(retry_after=__import__('time').time()+180,reason=r.stdout+r.stderr));sys.exit(78)
if mode=='setup':
 assert ssh(f'mkdir -p {BASE}/source-proof').returncode==0
 for local,remote in [('source-Cargo.toml','Cargo.toml'),('source-lib.rs','lib.rs')]:subprocess.run(['scp',str(ROOT/'tools/pv-cbmid-20261027'/local),f'{HOST}:{BASE}/source-proof/{remote}'],check=True)
 print('setup uploaded after admission');sys.exit()
op=extra[0]; namespace='PV_CBM_Op'+op+'Raw'
entries={'132':'pool_v1::hiding::pool_v1_pair_forest_relation_free_mask_cells_v1','133':'pool_v1::hiding::pool_v1_pair_forest_copy_active_rows_v1','134':'pool_v1::hiding::pool_v1_pair_forest_copy_active_row_masks_v1','79':'r0::encoder::eval_message'}
if mode=='charon':
 entry='pv_cbm_source::'+entries[op]
 include='pv_cbm_source::pool_v1::hiding::*' if op!='79' else 'pv_cbm_source::r0::*'
 args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={BASE}/charon-target',PIN+'/charon','cargo','--preset','aeneas','--mir','built','--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry,'--include',include,'--dest-file',BASE+'/'+namespace+'.llbc','--','--manifest-path',BASE+'/source-proof/Cargo.toml','--release','--offline','--lib','--jobs','4']
elif mode=='aeneas':
 assert ssh(f'mkdir -p {BASE}/op{op}-generated').returncode==0
 args=['timeout','120',PIN+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',BASE+'/op'+op+'-generated','-split-files','-emit-json',BASE+'/'+namespace+'.llbc']
else:raise ValueError(mode)
receipt=dict(target=args,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),expected_phase='optimized compile and selected built MIR extraction' if mode=='charon' else 'Aeneas translation',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),print_axioms='N/A extraction; no Lean theorem yet')
save(out/'target.json',receipt)
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',GATE+'/barrier.py',dest+'/admission-barrier.json','/usr/bin/time','-v','-o',dest+'/time.log',*args]
r=ssh(shlex.join(cmd)+f' > {dest}/output.log 2>&1');receipt['exit']=r.returncode
for f in ['output.log','time.log','admission-before.json','admission-barrier.json']:
 t=ssh('cat '+dest+'/'+f);(out/f).write_text(t.stdout+t.stderr)
t=(out/'time.log').read_text()
receipt['wall']=re.findall(r'Elapsed \(wall clock\) time.*: (.*)',t)
receipt['peak_rss_kib']=re.findall(r'Maximum resident set size \(kbytes\): (\d+)',t)
receipt['swap']=re.findall(r'Swaps: (\d+)',t)
for file in ([namespace+'.llbc'] if mode=='charon' else ['op'+op+'-generated/Funs.lean','op'+op+'-generated/Types.lean','op'+op+'-generated/ExternalFuns.lean','op'+op+'-generated/ExternalTypes.lean']):
 t=ssh('cat '+shlex.quote(BASE+'/'+file))
 if t.returncode==0:
  data=t.stdout.encode();receipt.setdefault('artifacts',{})[file]=dict(sha256=hashlib.sha256(data).hexdigest(),size=len(data))
  if len(data)<2000000:(out/Path(file).name).write_bytes(data)
save(out/'receipt.json',receipt)
print(mode,name,'exit',r.returncode);print((out/'output.log').read_text()[-5000:]);sys.exit(r.returncode)
