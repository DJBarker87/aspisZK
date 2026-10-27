from pathlib import Path
import subprocess,os,json,hashlib,time,signal
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
S=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
pins=json.loads((O/'XRa_release_sourcepins.json').read_text())
assert pins['source_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
errors=[]
for row in pins['files']:
 p=S/row['path']
 if not p.is_file():errors.append({'path':row['path'],'error':'missing'});continue
 h=hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 if h!=row['sha256']:errors.append({'path':row['path'],'actual':h,'expected':row['sha256']})
(B/'XRe_included_release_input_check.json').write_text(json.dumps({'root':str(S),'source_revision':pins['source_revision'],'files_checked':len(pins['files']),'errors':errors},indent=2)+'\n')
assert not errors,errors[:10]
charon=O/'XRa_bin/charon'
assert hashlib.file_digest(charon.open('rb'),'sha256').hexdigest()=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
opaque=['crate::compact::check_values','crate::verifier::echeck','crate::compact::expand_values','crate::verifier::candidate::wide_view','crate::verifier::checkpoint','crate::verifier::prepared_claim']
(B/'XRe_included_selector_delta.json').write_text(json.dumps({'opaque':opaque,'inherited_extra_selectors_removed':True,'source_and_translator_unchanged':True},indent=2)+'\n')
assert hashlib.file_digest((O/'XRa_bin/charon-driver').open('rb'),'sha256').hexdigest()=='efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--include','core::iter','--include','core::slice::iter','--start-from','crate::verifier::candidate::tx1']
for p in opaque:cmd+=['--opaque',p]
cmd+=['--dest-file',str(B/'XRe_included_release_candidate_tx1.llbc'),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--no-default-features','--features','private-leaf-salts','--jobs','1']
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(B/'XRe_included_release_target'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RAYON_NUM_THREADS='1')
for k in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(k,None)
env['RUSTFLAGS']='-Zthreads=1 -C link-arg=-Wl,--threads=1'
(B/'XRe_included_release_candidate_charon_command.json').write_text(json.dumps({'command':cmd,'env':{k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','RUSTFLAGS','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']},'namespace_selector_mapping':'inlined crate::aspis_core and crate::pool_v1 become actual dependency crate paths','feature_mapping':'historical kit r0 maps to release dependency r0; release crate feature private-leaf-salts retained'},indent=2)+'\n')
print('RELEASE_INPUT_PASS',len(pins['files']),flush=True);print('COMMAND',cmd,flush=True)
cg=Path('/sys/fs/cgroup')/next(x.split(':',2)[2].strip().lstrip('/') for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0:'))
peak=0;start=time.monotonic();stopped=None
p=subprocess.Popen(cmd,cwd=S,env=env,start_new_session=True)
while p.poll() is None:
 peak=max(peak,int((cg/'memory.current').read_text()))
 if peak>=int(7.5*2**30) or time.monotonic()-start>=500:
  stopped='memory review threshold 7.5GiB' if peak>=int(7.5*2**30) else '500s extraction review point'
  os.killpg(p.pid,signal.SIGTERM);break
 time.sleep(.5)
try:p.wait(timeout=10)
except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
llbc=B/'XRe_included_release_candidate_tx1.llbc'
result={'exit':p.returncode,'wall_seconds':time.monotonic()-start,'sampled_cgroup_peak_bytes':peak,'stopped':stopped,'llbc_sha256':hashlib.file_digest(llbc.open('rb'),'sha256').hexdigest() if llbc.exists() else None,'llbc_bytes':llbc.stat().st_size if llbc.exists() else None}
if llbc.exists():
 raw=json.loads(llbc.read_text());result['llbc_has_errors']=raw.get('has_errors');result['function_declarations']=len(raw['translated']['fun_decls']);result['type_declarations']=len(raw['translated']['type_decls'])
(B/'XRe_included_release_candidate_charon_result.json').write_text(json.dumps(result,indent=2)+'\n');print('RESULT',json.dumps(result),flush=True)
assert p.returncode==0 and result.get('llbc_has_errors') is False and result.get('function_declarations',0)>0,result
