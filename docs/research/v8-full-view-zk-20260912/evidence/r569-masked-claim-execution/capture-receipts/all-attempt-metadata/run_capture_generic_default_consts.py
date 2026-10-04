#!/usr/bin/env python3
"""Changed-dependency R569 Charon capture; preserve original successful capture."""
import hashlib, json, pathlib, shlex, subprocess
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
HOST='dombarker@100.108.41.90'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SCP=['scp','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
old=json.loads((HERE/'R569-prelaunch.json').read_text())
source=old['source_root']; stage=old['stage_root']
charon='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
flags=old['rustflags']; flags_sha=old['rustflags_file_sha256']
assert hashlib.sha256((WORKTREE/'docs/research/v8-full-view-zk-20260912/evidence/r555-zero-output-rejoin/selected-rustflags.txt').read_bytes()).hexdigest()==flags_sha
remote=r'''import hashlib,json,os,pathlib,subprocess,sys
source=pathlib.Path(@SOURCE@); stage=pathlib.Path(@STAGE@); charon=pathlib.Path(@CHARON@)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def tree(root): return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file()}
assert stage.is_dir() and source.is_dir() and charon.is_file()
old=json.loads((stage/'R569-prelaunch.json').read_text())
assert old['source_core_src_files']==@EXPECTED_CORE@
assert old['stage_host_relation_callback_with_single_probe_sha256']==@EXPECTED_CB@
assert sha(stage/'R569MaskedClaim.llbc')==@EXPECTED_OLD_LLBC@
assert sha(stage/'R569MaskedClaimWithFrom.llbc')=='e1670d259f43aa411c49fd7e763814a4d790358b0e8f008184424c032f2bbc81'
assert sha(stage/'R569MaskedClaimGeneric.llbc')=='1be255f75d13fe10d487b6415e9bd4a546ed4f5f3304fe1c28764308d9fda5d0'
assert sha(charon)==@EXPECTED_CHARON@
assert tree(source/'crates/aspis-core/src')==@EXPECTED_CORE@
assert tree(stage/'crates/aspis-core/src')==@EXPECTED_CORE@
assert sha(source/'crates/aspis-core/src/state_only_hiding.rs')==@EXPECTED_STATE@
assert sha(stage/'docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs')==@EXPECTED_CB@
assert sha(source/'crates/aspis-core/Cargo.toml')==@EXPECTED_CORE_CARGO@
assert sha(stage/'crates/aspis-core/Cargo.toml')==@EXPECTED_CORE_CARGO@
assert sha(source/'crates/aspis-core/build.rs')==@EXPECTED_BUILD@
assert sha(stage/'crates/aspis-core/build.rs')==@EXPECTED_BUILD@
assert sha(source/'Cargo.lock')==@EXPECTED_LOCK@ and sha(stage/'Cargo.lock')==@EXPECTED_LOCK@
hostrel=pathlib.Path('docs/research/v8-no-work-100-20260907/experiments')
assert sha(source/hostrel/'performance-host/Cargo.toml')==@EXPECTED_HOST_CARGO@
assert sha(stage/hostrel/'performance-host/Cargo.toml')==@EXPECTED_HOST_CARGO@
assert sha(source/hostrel/'performance-host/Cargo.lock')==@EXPECTED_HOST_LOCK@
assert sha(stage/hostrel/'performance-host/Cargo.lock')==@EXPECTED_HOST_LOCK@
assert sha(source/hostrel/'relation_callback.rs')==@EXPECTED_CB_ORIGINAL@
manifest=stage/hostrel/'performance-host/Cargo.toml'
assert 'selected-v7-kernels' in manifest.read_text() and 'insecure-spend-fixture' in manifest.read_text()
flags=@FLAGS@
assert hashlib.sha256(json.dumps(__import__('shlex').split(flags),separators=(',',':')).encode()).hexdigest()==@EXPECTED_FLAGS_NORM@
env=os.environ.copy(); env.update({'PATH':'/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':flags,'CARGO_TARGET_DIR':str(source/hostrel/'performance-host/target')})
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::claim_probe']
includes=['core::option','core::result::_::map_err','aspis_core::state_only_hiding::begin_state_only_masked_sumcheck','aspis_core::state_only_hiding::_::from','aspis_core::transcript','aspis_core::field']
for i in includes: cmd += ['--include',i]
llbc=stage/'R569MaskedClaimGenericDefaultConsts.llbc'; assert not llbc.exists()
cmd += ['--dest-file',str(llbc),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(manifest),'--bin','aspis-v8-performance-host']
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 p=line.split()
 if p and p[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',p[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit(): reservations.append((p[0],int(v)))
assert sum(v for _,v in reservations)+7*1024**3<=40*1024**3,reservations
pre={'target':'R569 generic non-monomorphized default-const target-only R569 recapture including source-defined From conversion','previous_llbc_sha256':@EXPECTED_OLD_LLBC@,'source_revision':old['source_revision'],'source_freeze_revision':old['source_freeze_revision'],'source_root':str(source),'stage_root':str(stage),'source_core_src_files':@EXPECTED_CORE@,'source_core_state_only_hiding_sha256':@EXPECTED_STATE@,'source_core_build_sha256':@EXPECTED_BUILD@,'source_core_cargo_sha256':@EXPECTED_CORE_CARGO@,'source_cargo_lock_sha256':@EXPECTED_LOCK@,'host_cargo_sha256':@EXPECTED_HOST_CARGO@,'host_lock_sha256':@EXPECTED_HOST_LOCK@,'host_relation_callback_sha256':@EXPECTED_CB@,'charon_sha256':sha(charon),'rustflags':flags,'rustflags_sha256':@EXPECTED_FLAGS_FILE@,'rustflags_normalized_sha256':@EXPECTED_FLAGS_NORM@,'overflow_checks':True,'toolchain':'nightly-2026-06-01','argv':cmd,'includes':includes,'active_aspis_service_reservations_before_launch':reservations,'scope_memory_max_bytes':7*1024**3,'aggregate_reserved_max_bytes':40*1024**3,'phase':'non-monomorphized default-const focused target-only Charon extraction; no translation'}
pre['previous_captures']={'R569MaskedClaim.llbc':@EXPECTED_OLD_LLBC@,'R569MaskedClaimWithFrom.llbc':'e1670d259f43aa411c49fd7e763814a4d790358b0e8f008184424c032f2bbc81','R569MaskedClaimGeneric.llbc':'1be255f75d13fe10d487b6415e9bd4a546ed4f5f3304fe1c28764308d9fda5d0'}
(stage/'R569-generic-default-prelaunch.json').write_text(json.dumps(pre,indent=2)+'\n')
with (stage/'R569-generic-default.log').open('w') as out, (stage/'R569-generic-default.time.log').open('w') as tim:
 result=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=out,stderr=tim,env=env)
status={'exit_status':result.returncode,'llbc_exists':llbc.is_file(),'llbc_sha256':sha(llbc) if llbc.is_file() else None,'llbc_bytes':llbc.stat().st_size if llbc.is_file() else None,'formal_axioms':'N/A; LLBC capture only','translation':'not run'}
if llbc.is_file():
 try: status['has_errors']=json.loads(llbc.read_text()).get('has_errors')
 except Exception as e: status['json_error']=repr(e)
(stage/'R569-generic-default-result.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status),flush=True); sys.exit(result.returncode)
'''
def lit(s): return repr(s)
values={
'SOURCE':source,'STAGE':stage,'CHARON':charon,'EXPECTED_CORE':old['source_core_src_files'],'EXPECTED_CB':old['stage_host_relation_callback_with_single_probe_sha256'],'EXPECTED_OLD_LLBC':'f359adc969db6fee290f0dab7d7c5cd7834918934ecf56b54d223b70f4022962','EXPECTED_CHARON':old['charon_sha256'],'EXPECTED_STATE':old['source_core_src_files']['state_only_hiding.rs'],'EXPECTED_CORE_CARGO':old['source_core_cargo_sha256'],'EXPECTED_BUILD':old['source_core_build_sha256'],'EXPECTED_LOCK':old['source_cargo_lock_sha256'],'EXPECTED_HOST_CARGO':old['host_cargo_sha256'],'EXPECTED_HOST_LOCK':old['host_lock_sha256'],'EXPECTED_CB_ORIGINAL':old['host_relation_callback_original_sha256'],'EXPECTED_FLAGS_NORM':old['rustflags_normalized_sha256'],'EXPECTED_FLAGS_FILE':flags_sha,'FLAGS':flags}
for k,v in values.items(): remote=remote.replace('@'+k+'@',lit(v))
unit='aspis-r569-generic-default-20261004'
cmd=['systemd-run','--user','--wait','--collect','--pipe',f'--unit={unit}',f'--working-directory={source}','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',remote]
(HERE/'R569-generic-default-launch.json').write_text(json.dumps({'unit':unit,'systemd_argv':cmd,'only_change':'omit --consts values only; default const mode; other argv/source/include selectors unchanged','caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'old_capture_immutable_sha256':'f359adc969db6fee290f0dab7d7c5cd7834918934ecf56b54d223b70f4022962'},indent=2)+'\n')
with (HERE/'R569-generic-default-ssh-output.log').open('w') as out:
 r=subprocess.run([*SSH,HOST,shlex.join(cmd)],stdout=out,stderr=subprocess.STDOUT)
(HERE/'R569-generic-default-launch-exit.txt').write_text(str(r.returncode)+'\n')
for rel in ['R569-generic-default-prelaunch.json','R569-generic-default.log','R569-generic-default.time.log','R569-generic-default-result.json','R569MaskedClaimGenericDefaultConsts.llbc']:
 scp=subprocess.run([*SCP,f'{HOST}:{stage}/{rel}',str(HERE/rel)])
 if scp.returncode: raise SystemExit(scp.returncode)
if r.returncode: raise SystemExit(r.returncode)
