from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
W=Path(__file__).resolve().parent
phase=sys.argv[1]
assert phase in {'charon','aeneas'}
G=1024**3
inp=W/'input'; cut=inp/'source-cut'; pins=json.loads((inp/'sourcecut-pins.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,want in pins['source_cut_files'].items(): assert sha(cut/name)==want, name
assert sha(inp/'pins/candidate-weights.rs')==pins['candidate_weights_sha256']
assert sha(inp/'pins/frozen-weights.rs')==pins['frozen_weights_sha256']
assert pins['candidate_pair_body_sha256']==pins['frozen_pair_body_sha256']
tools=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
charon=tools/'charon-target/release/charon'; aeneas=tools/'bin/aeneas'
toolpins={str(charon):'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',str(aeneas):'959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'}
for p,h in toolpins.items(): assert sha(Path(p))==h,p
cgline=Path('/proc/self/cgroup').read_text().strip(); assert cgline.startswith('0::'),cgline
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
run=W/'runs'/phase;run.mkdir(parents=True,exist_ok=False)
if phase=='charon':
 llbc=run/'pair-caller-step.llbc'
 cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default',
  '--include','core::iter::traits::iterator::Iterator::fold','--include','core::option::Option','--include','core::result::Result',
  '--start-from',pins['charon_start_from']]
 for opaque in pins['opaque_operation_boundaries']: cmd.extend(['--opaque',opaque])
 cmd.extend(['--dest-file',str(llbc),'--','--locked','--offline','--release','--lib','--no-default-features','--features','r0,private-leaf-salts','--jobs','1'])
 cwd=cut; env=os.environ.copy();env.update({'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_TARGET_DIR':'/home/dombarker/project-offloads/s3-s9-scalar-fold-fullsysroot-v3-20261021/target','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true'})
 expected='Warm-cache scoped Charon extraction for exact candidate helper-call and four-cell update projection; no full pair target'
else:
 prev=json.loads((W/'runs/charon/receipt.json').read_text());assert prev['exit_status']==0 and prev['candidate_llbc_sha256']
 llbc=W/'runs/charon/pair-caller-step.llbc'; obj=json.loads(llbc.read_text());assert obj and not obj['has_errors']
 gen=run/'generated';cmd=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1S9PairCallerStepV1','-dest',str(gen),'-subdir','AspisR1S9PairCallerStepV1','-split-files','-emit-json',str(llbc)]
 cwd=cut;env=os.environ.copy();env.update({'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'})
 expected='Aeneas translation of inspected caller-step LLBC only; no toolchain rebuild'
for key in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'):env.pop(key,None)
command={'phase':phase,'argv':cmd,'cwd':str(cwd),'limits':limits,'cgroup':str(cg),'tool_pins':toolpins,'candidate_weights_sha256':pins['candidate_weights_sha256'],'frozen_weights_sha256':pins['frozen_weights_sha256'],'source_cut_lib_sha256':sha(cut/'lib.rs'),'sourcecut_pins_sha256':sha(inp/'sourcecut-pins.json'),'expected_work':expected,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(run/'command.json').write_text(json.dumps(command,indent=2)+'\n');(run/'environment.json').write_text(json.dumps({k:env.get(k) for k in ('PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')},indent=2)+'\n')
before=(cg/'memory.events').read_text();start=time.monotonic();timed=False
with (run/'stdout.log').open('x') as out:
 proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(run/'time.log'),*cmd],cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  if time.monotonic()-start>180:
   timed=True;os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  time.sleep(.1)
status=proc.returncode;wall=time.monotonic()-start;after=(cg/'memory.events').read_text()
receipt={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(wall,3),'peak_process_rss_kib':None,'swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':after,'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
try:
 t=(run/'time.log').read_text();import re
 m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)
 if m:receipt['peak_process_rss_kib']=int(m.group(1))
except Exception:pass
if phase=='charon' and (run/'pair-caller-step.llbc').exists():
 raw=json.loads((run/'pair-caller-step.llbc').read_text());tr=raw['translated']; names=[]
 for d in tr.get('fun_decls',[]):
  name=d['item_meta'].get('name',[]);text='::'.join(str(x.get('Ident',[''])[0]) if 'Ident' in x else '' for x in name)
  if any(k in text for k in ('pair_step_root','pair_s2_libra_parts_projection','factored_s2_libra_weights')):names.append({'def_id':d['def_id'],'name':text,'opacity':d['item_meta'].get('opacity')})
 receipt['candidate_llbc_sha256']=sha(run/'pair-caller-step.llbc');receipt['functions_of_interest']=names;receipt['contains_projection']=any('pair_s2_libra_parts_projection' in x['name'] for x in names);receipt['contains_root']=any('pair_step_root' in x['name'] for x in names);receipt['has_errors']=raw.get('has_errors')
if phase=='aeneas' and (run/'generated/translation.json').exists():
 receipt['generated_translation_sha256']=sha(run/'generated/translation.json')
 for p in sorted((run/'generated').rglob('*.lean')):receipt.setdefault('generated_files',{})[str(p.relative_to(run))]=sha(p)
(run/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));sys.exit(status if status is not None else 1)
