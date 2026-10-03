#!/usr/bin/env python3
"""Launch only after explicit lead review of an exact R427 observer build receipt."""
import argparse, hashlib, json, os, pathlib, shlex, subprocess, sys
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[2]
PREFLIGHT=HERE.parent
R396_PLAN=WORKTREE/'.r21-scratch/r396-private-batch-unmonomorphized-plan/extract-command.json'
R396_LLBC=WORKTREE/'.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
EXPECTED_R396='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
EXPECTED_WRAPPER='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
EXPECTED_ORIGINAL_DRIVER='4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938'
EXPECTED_CHARON_LOCK='c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67'
EXPECTED_GET_MIR='246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab'
EXPECTED_RUSTC='14210df0e27ccd7d9e6a05b8085cbd438e4bbc65'
RUSTC='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc'
HOST='dombarker@100.108.41.90'
SSH_OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SOURCE_ROOT='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
CANDIDATE_ROOT='/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a'
CAPTURE_ROOT='/home/dombarker/project-offloads/aspis-r427-raw-mir-capture-20261002-a'
WRAPPER=CANDIDATE_ROOT+'/observer-bin/charon'
DRIVER=CANDIDATE_ROOT+'/observer-bin/charon-driver'
ORIGINAL_WRAPPER='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
ORIGINAL_DRIVER='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon-driver'
REMOTE_BASELINE='/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc'
SOURCE_HASHES={
 'r110_norm.rs':'8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e',
 'circle_norm.rs':'3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2',
 'line_norm.rs':'4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528',
 'joined_inverse.rs':'ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb',
 'aspis_core_field.rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499',
 'performance_host_Cargo.toml':'62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c',
 'performance_host_Cargo.lock':'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814'}
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
R396_TOOLCHAIN=(WORKTREE/'.r21-scratch/r396-private-batch-unmonomorphized-plan/toolchain.txt').read_text()
assert f'rustc_commit={EXPECTED_RUSTC}' in R396_TOOLCHAIN
assert f'charon_driver_sha256={EXPECTED_ORIGINAL_DRIVER}' in R396_TOOLCHAIN
def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--reviewed-build-receipt',type=pathlib.Path,required=True)
 ap.add_argument('--reviewed-build-receipt-sha256',required=True)
 ap.add_argument('--launch-revision',required=True,help='git revision recorded at launch time')
 args=ap.parse_args()
 if os.environ.get('R427_ALLOW_LAUNCH')!='1': raise SystemExit('R427 preparation only: set R427_ALLOW_LAUNCH=1 after lead authorizes the exact command.')
 receipt=json.loads(args.reviewed_build_receipt.read_text())
 receipt_sha=sha(args.reviewed_build_receipt)
 if receipt_sha!=args.reviewed_build_receipt_sha256: raise SystemExit('reviewed build-receipt SHA mismatch')
 # Fail closed unless the receipt attests the exact source/build outputs reviewed by the lead.
 required={'candidate_root':CANDIDATE_ROOT,'wrapper_path':WRAPPER,'driver_path':DRIVER,'wrapper_sha256':EXPECTED_WRAPPER,'original_driver_sha256':EXPECTED_ORIGINAL_DRIVER,'charon_lock_sha256':EXPECTED_CHARON_LOCK,'build_exit_status':0,'rustc_commit':EXPECTED_RUSTC,'source_commit':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','reviewed':True}
 for k,v in required.items():
  if receipt.get(k)!=v: raise SystemExit(f'build-receipt gate failed for {k}: {receipt.get(k)!r} != {v!r}')
 driver_sha=receipt.get('driver_sha256','')
 if len(driver_sha)!=64 or any(c not in '0123456789abcdef' for c in driver_sha): raise SystemExit('receipt lacks a valid candidate driver_sha256')
 candidate_get_mir=receipt.get('candidate_get_mir_sha256','')
 if candidate_get_mir!=EXPECTED_GET_MIR: raise SystemExit('receipt candidate get_mir source hash does not match reviewed input')
 patch_sha=receipt.get('reviewed_patch_sha256','')
 for label,value in [('candidate_get_mir_sha256',candidate_get_mir),('reviewed_patch_sha256',patch_sha)]:
  if len(value)!=64 or any(c not in '0123456789abcdef' for c in value): raise SystemExit(f'build receipt lacks valid {label}')
 if sha(R396_LLBC)!=EXPECTED_R396: raise SystemExit('local R396 baseline checksum changed')
 old=json.loads(R396_PLAN.read_text())
 if old['verified_source_hashes']!=SOURCE_HASHES: raise SystemExit('saved R396 source hashes do not match the fixed task hashes')
 if old['source_revision_recorded']!='13617a70553ed3c43cee312acba2407b29a7052d': raise SystemExit('unexpected R396 source snapshot revision record')
 if old['start_from']!=['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch'] or old['monomorphize'] is not False: raise SystemExit('R396 root/monomorphization settings changed')
 if '--print-original-ullbc' in old['command']: raise SystemExit('R427 must not add print-original-ullbc')
 if '--dest-file' not in old['command']: raise SystemExit('R396 saved command lacks destination')
 launch={'reviewed_build_receipt':str(args.reviewed_build_receipt),'reviewed_build_receipt_sha256':receipt_sha,'candidate_driver_sha256':driver_sha,'candidate_get_mir_sha256':candidate_get_mir,'reviewed_patch_sha256':patch_sha,'launch_revision':args.launch_revision}
 # Remote code revalidates source/cache/baseline and cap/reservation before creating anything.
 remote=r'''import os,pathlib,hashlib,subprocess,json,shlex,shutil,re
source_root=pathlib.Path("@SOURCE_ROOT@")
experiments=source_root/'docs/research/v8-no-work-100-20260907/experiments'
workspace=experiments/'performance-host'
candidate=pathlib.Path("@CANDIDATE_ROOT@")
root=pathlib.Path("@CAPTURE_ROOT@")
root_preexisting=root.exists()
root_created=False
wrapper=pathlib.Path("@WRAPPER@")
driver=pathlib.Path("@DRIVER@")
original_wrapper=pathlib.Path("@ORIGINAL_WRAPPER@")
original_driver=pathlib.Path("@ORIGINAL_DRIVER@")
baseline=pathlib.Path("@REMOTE_BASELINE@")
rustc=pathlib.Path("@RUSTC@")
expected={"r110_norm.rs":"8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e","circle_norm.rs":"3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2","line_norm.rs":"4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528","joined_inverse.rs":"ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb","aspis_core_field.rs":"639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499","performance_host_Cargo.toml":"62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c","performance_host_Cargo.lock":"a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814"}
paths={"r110_norm.rs":experiments/'r110_norm.rs',"circle_norm.rs":experiments/'circle_norm.rs',"line_norm.rs":experiments/'line_norm.rs',"joined_inverse.rs":experiments/'joined_inverse.rs',"aspis_core_field.rs":source_root/'crates/aspis-core/src/field.rs',"performance_host_Cargo.toml":workspace/'Cargo.toml',"performance_host_Cargo.lock":workspace/'Cargo.lock'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def effective_cgroup():
    rel=next(line.split('::',1)[1].lstrip('/') for line in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
    cg=pathlib.Path('/sys/fs/cgroup')/rel
    names=['memory.high','memory.max','memory.swap.max','pids.max','memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events','pids.current']
    return {'path':str(cg),**{n:(cg/n).read_text().strip() if (cg/n).exists() else None for n in names}}
actual={k:sha(v) for k,v in paths.items()}
assert actual==expected,(actual,expected)
assert sha(baseline)=="@BASELINE_SHA@", "R396 baseline changed"
assert sha(wrapper)=="@WRAPPER_SHA@", "candidate wrapper does not match reviewed unchanged wrapper"
assert sha(driver)=="@DRIVER_SHA@", "candidate driver does not match reviewed build receipt"
assert sha(original_wrapper)=="@WRAPPER_SHA@", "original wrapper changed"
assert sha(original_driver)=="@ORIGINAL_DRIVER_SHA@", "original driver changed from R396 toolchain pin"
charon_toolchain=subprocess.check_output([str(wrapper),'toolchain-version'],text=True).strip()
assert charon_toolchain=='nightly-2026-06-01',charon_toolchain
charon_sysroot=subprocess.check_output([str(wrapper),'toolchain-path'],text=True).strip()
rustc_version=subprocess.check_output([str(rustc),'-Vv'],text=True)
assert "commit-hash: @RUSTC_COMMIT@" in rustc_version,rustc_version
assert sha(candidate/'charon/Cargo.lock')=="@CHARON_LOCK_SHA@", "candidate Charon Cargo.lock differs from pinned source"
assert sha(candidate/'charon/src/bin/charon-driver/translate/get_mir.rs')=="@GET_MIR_SHA@", "candidate hook source differs from reviewed build receipt"
assert not root.exists(),f"capture root already exists: {root}"
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
mem_total=int(mem['MemTotal'].split()[0])*1024; mem_avail=int(mem['MemAvailable'].split()[0])*1024
candidate_max=7*1024**3; required=24*1024**3; safe=min(40*1024**3,mem_total-16*1024**3)
assert mem_avail-candidate_max>=required,(mem,candidate_max,required)
effective_before=effective_cgroup()
assert (effective_before['memory.high'],effective_before['memory.max'],effective_before['memory.swap.max'],effective_before['pids.max'])==('5368709120','7516192768','0','128'),effective_before
assert candidate_max<=safe,(candidate_max,safe)
slices=[]
for line in subprocess.check_output(['systemctl','--user','list-units','--all','--type=slice','--no-legend'],text=True).splitlines():
 name=line.split()[0]
 if not name.startswith('aspis'): continue
 props=subprocess.check_output(['systemctl','--user','show',name,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True)
 d=dict(x.split('=',1) for x in props.splitlines() if '=' in x); cg=pathlib.Path('/sys/fs/cgroup')/d.get('ControlGroup','').lstrip('/')
 pids=[]
 if cg.exists():
  for f in cg.rglob('cgroup.procs'):
   try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
   except OSError:pass
 slices.append({'unit':name,'pids':pids,'MemoryMax':d.get('MemoryMax'),'MemoryCurrent':d.get('MemoryCurrent')})
assert not any(x['pids'] for x in slices),slices
active_slice_memory_max=sum(int(x['MemoryMax']) for x in slices if x['pids'] and str(x.get('MemoryMax','')).isdigit())
assert active_slice_memory_max+candidate_max<=safe,(active_slice_memory_max,candidate_max,safe)
active_services=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
other_active_aspis=[line.strip() for line in active_services.splitlines() if line.split() and line.split()[0].startswith('aspis') and line.split()[0]!='aspis-r427-raw-mir-capture.service']
assert not other_active_aspis,other_active_aspis
heavy=[x.strip() for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if len(x.split())>1 and x.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')]
assert not heavy,heavy
assert sha(candidate/'charon/Cargo.lock')=="@CHARON_LOCK_SHA@", "candidate locked toolchain inputs differ from reviewed pinned source"
root.mkdir()
root_created=True
(root/'preserved-original-binaries').mkdir()
shutil.copy2(original_wrapper,root/'preserved-original-binaries/charon-wrapper')
shutil.copy2(original_driver,root/'preserved-original-binaries/charon-driver')
assert sha(root/'preserved-original-binaries/charon-wrapper')=="@WRAPPER_SHA@"
assert sha(root/'preserved-original-binaries/charon-driver')=="@ORIGINAL_DRIVER_SHA@"
fps=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
flags=[json.loads(p.read_text())['rustflags'] for p in fps]
assert flags and all(f==flags[0] for f in flags)
expected_flags=@EXPECTED_RUSTFLAGS@
assert flags[0]==expected_flags
assert hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest()=="@RUSTFLAGS_SHA@"
os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
os.environ['RUSTFLAGS']=shlex.join(flags[0])
command=[str(wrapper),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',@ROOT@]
for inc in @INCLUDES@: command.extend(['--include',inc])
command += ['--dest-file',str(root/'R427RawMirCapture.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(workspace/'Cargo.toml'),'--bin','aspis-v8-performance-host']
assert '--print-original-ullbc' not in command
baseline_before=sha(baseline)
record={'source_hashes_before':actual,'baseline_sha_before':baseline_before,'wrapper_sha256':sha(wrapper),'driver_sha256':sha(driver),'candidate_driver_sha256':sha(driver),'rustflags_sha256':"@RUSTFLAGS_SHA@",'rustflags':flags[0],'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'host_meminfo_before':mem,'effective_cgroup_before':effective_before,'existing_aspis_slices':slices,'active_slice_memory_max_bytes':active_slice_memory_max,'candidate_memory_max_bytes':candidate_max,'safe_working_limit_bytes':safe,'other_active_aspis_services':other_active_aspis,'heavy_processes':heavy,'reviewed_build_receipt_sha256':'@RECEIPT_SHA@','launch_revision':'@LAUNCH_REV@'}
(root/'host-reservation-before.json').write_text(json.dumps(record,indent=2))
(root/'extract-command.json').write_text(json.dumps({'command':command,'start_from':@ROOTS@,'include':@INCLUDES@,'features':'insecure-spend-fixture,selected-v7-kernels','monomorphize':False,'environment':{'ASPIS_R427_OBSERVE_MIR':'1'},'source_hashes':actual,'baseline_sha256':sha(baseline),'reviewed_build_receipt_sha256':'@RECEIPT_SHA@'},indent=2))
# Raw observer is opt-in and diagnostics only; no --print-original-ullbc option is added.
os.environ['ASPIS_R427_OBSERVE_MIR']='1'
with (root/'charon.stdout.log').open('wb') as so, (root/'charon.stderr.log').open('wb') as se:
 run=subprocess.run(['/usr/bin/time','-v','-o',str(root/'gnu-time.txt'),*command],stdout=so,stderr=se)
source_after={k:sha(v) for k,v in paths.items()}
baseline_after=sha(baseline)
(root/'host-reservation-after.json').write_text(json.dumps({'source_hashes_after':source_after,'baseline_sha_after':baseline_after,'host_meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'effective_cgroup_after':effective_cgroup(),'rustc_version_verbose':rustc_version},indent=2))
assert source_after==expected,source_after
assert baseline_after=="@BASELINE_SHA@",baseline_after
llbc=root/'R427RawMirCapture.llbc'
gtxt=(root/'gnu-time.txt').read_text()
def metric(pattern):
 m=re.search(pattern,gtxt,re.M); return m.group(1).strip() if m else None
result={'charon_exit_status':run.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'), 'peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0), 'swap_count':int(metric(r'Swaps:\s*(\d+)') or 0), 'gnu_time_exit_status':int(metric(r'Exit status:\s*(\d+)') or -1),'llbc_exists':llbc.is_file(),'llbc_sha256':sha(llbc) if llbc.is_file() else None,'observer_stdout_sha256':sha(root/'charon.stdout.log'),'observer_stdout_bytes':(root/'charon.stdout.log').stat().st_size,'observer_stderr_sha256':sha(root/'charon.stderr.log'),'observer_stderr_bytes':(root/'charon.stderr.log').stat().st_size,'candidate_driver_sha256':sha(driver),'reviewed_build_receipt_sha256':'@RECEIPT_SHA@','candidate_get_mir_sha256':'@GET_MIR_SHA@','reviewed_patch_sha256':'@PATCH_SHA@','source_commit':'@SOURCE_COMMIT@','baseline_sha256_before_after':[baseline_before,baseline_after],'source_hashes_before_after':{'before':actual,'after':source_after},'source_revision_recorded':'13617a70553ed3c43cee312acba2407b29a7052d','capture_revision':'@LAUNCH_REV@','requested_root':@ROOT@,'has_errors':json.loads(llbc.read_text()).get('has_errors') if llbc.is_file() else None,'rustc_version_verbose':rustc_version,'charon_toolchain':charon_toolchain,'charon_sysroot':charon_sysroot,'frame_marker_counts':{k:root.joinpath('charon.stderr.log').read_text(errors='replace').count(k) for k in ['ASPIS_R427_RAW_MIR_BEGIN','ASPIS_R427_RAW_MIR_END','ASPIS_R427_STATEMENT_SOURCE','ASPIS_R427_USE_RETAG','ASPIS_R427_TERMINATOR_SOURCE','ASPIS_R427_CALL_ARG']},'formal_axioms':'N/A; diagnostic LLBC only'}
(root/'result.json').write_text(json.dumps(result,indent=2))
print('R427_CHILD_EXIT',run.returncode)
raise SystemExit(run.returncode)
'''
 replacements={
      '@SOURCE_ROOT@':SOURCE_ROOT,'@CANDIDATE_ROOT@':CANDIDATE_ROOT,'@CAPTURE_ROOT@':CAPTURE_ROOT,'@WRAPPER@':WRAPPER,'@DRIVER@':DRIVER,'@ORIGINAL_WRAPPER@':ORIGINAL_WRAPPER,'@ORIGINAL_DRIVER@':ORIGINAL_DRIVER,'@REMOTE_BASELINE@':REMOTE_BASELINE,'@RUSTC@':RUSTC,'@RUSTC_COMMIT@':EXPECTED_RUSTC,'@BASELINE_SHA@':EXPECTED_R396,'@WRAPPER_SHA@':EXPECTED_WRAPPER,'@DRIVER_SHA@':driver_sha,'@ORIGINAL_DRIVER_SHA@':EXPECTED_ORIGINAL_DRIVER,'@CHARON_LOCK_SHA@':EXPECTED_CHARON_LOCK,'@GET_MIR_SHA@':EXPECTED_GET_MIR,'@PATCH_SHA@':patch_sha,'@SOURCE_COMMIT@':receipt.get('source_commit'),'@RUSTFLAGS_SHA@':old['rustflags_sha256'],'@EXPECTED_RUSTFLAGS@':repr(old['rustflags']),'@ROOT@':repr(old['start_from'][0]),'@ROOTS@':json.dumps(old['start_from']),'@INCLUDES@':json.dumps(old['include']),'@RECEIPT_SHA@':receipt_sha,'@LAUNCH_REV@':args.launch_revision}
 for k,v in replacements.items(): remote=remote.replace(k,v)
 if '@' in remote: raise SystemExit('unresolved remote-script placeholder')
 # Preserve failure/status evidence if an assertion or runtime gate fails before extraction completes.
 import textwrap
 body=remote
 remote="import pathlib,json,traceback\ntry:\n"+textwrap.indent(body,'    ')+"\nexcept SystemExit as exc:\n    if 'root' in globals() and not root_preexisting:\n        root.mkdir(parents=True,exist_ok=True)\n        details={'status':'SystemExit','code':exc.code,'traceback':traceback.format_exc(),'source_hashes_before':globals().get('actual'),'source_hashes_after':globals().get('source_after'),'baseline_before':globals().get('baseline_before'),'baseline_after':globals().get('baseline_after'),'effective_cgroup':globals().get('effective_before'),'formal_axioms':'N/A; diagnostic only'}\n        (root/'runner-status.json').write_text(json.dumps(details,indent=2))\n    raise\nexcept BaseException as exc:\n    if 'root' in globals() and not root_preexisting:\n        root.mkdir(parents=True,exist_ok=True)\n        details={'status':'exception','failure':repr(exc),'traceback':traceback.format_exc(),'source_hashes_before':globals().get('actual'),'source_hashes_after':globals().get('source_after'),'baseline_before':globals().get('baseline_before'),'baseline_after':globals().get('baseline_after'),'effective_cgroup':globals().get('effective_before'),'formal_axioms':'N/A; diagnostic only'}\n        (root/'early-failure.json').write_text(json.dumps(details,indent=2))\n    raise\n"
 caps=['--user','--wait','--collect','--pipe','--unit=aspis-r427-raw-mir-capture','--working-directory='+SOURCE_ROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128']
 remote_shell_command=shlex.join(['systemd-run',*caps,'python3','-c',remote])
 ssh_cmd=['ssh',*SSH_OPTS,HOST,remote_shell_command]
 local=HERE/'r427-remote-script.materialized.py'
 local.write_text(remote)
 local_argv=HERE/'r427-ssh-argv.json'
 (HERE/'reviewed-build-receipt.snapshot.json').write_bytes(args.reviewed_build_receipt.read_bytes())
 local_argv.write_text(json.dumps({'ssh_argv':ssh_cmd,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'build_receipt_sha256':receipt_sha,'candidate_driver_sha256':driver_sha},indent=2)+'\n')
 # This post-run collection is intentionally separate from extraction and is not invoked during preparation.
 ssh_result=subprocess.run(ssh_cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,check=False)
 (HERE/'ssh-launch.log').write_text(ssh_result.stdout)
 (HERE/'launch-status.json').write_text(json.dumps({'ssh_returncode':ssh_result.returncode,'build_receipt_sha256':receipt_sha,'candidate_driver_sha256':driver_sha,'candidate_get_mir_sha256':candidate_get_mir,'reviewed_patch_sha256':patch_sha,'candidate_root':CANDIDATE_ROOT,'wrapper_path':WRAPPER,'driver_path':DRIVER,'wrapper_sha256':receipt.get('wrapper_sha256'),'original_driver_sha256':receipt.get('original_driver_sha256'),'charon_lock_sha256':receipt.get('charon_lock_sha256'),'build_exit_status':receipt.get('build_exit_status'),'reviewed':receipt.get('reviewed'),'source_commit':receipt.get('source_commit'),'rustc_commit':receipt.get('rustc_commit'),'launch_revision':args.launch_revision},indent=2)+'\n')
 if ssh_result.returncode!=0:
  (HERE/'remote-failure-receipt.json').write_text(json.dumps({'ssh_returncode':ssh_result.returncode,'remote_stdout_stderr_sha256':hashlib.sha256(ssh_result.stdout.encode()).hexdigest(),'remote_stdout_stderr_bytes':len(ssh_result.stdout.encode()),'launch_revision':args.launch_revision,'build_receipt_sha256':receipt_sha,'formal_axioms':'N/A; no LLBC theorem run'},indent=2)+'\n')
 # The fixed diagnostic runner can execute exactly once; copy receipts/logs/output before checking saved bytes.
 local_capture.mkdir()
 collection=[]
 def collect_if_present(relative):
  remote_path=f'{CAPTURE_ROOT}/{relative}'
  probe_cmd=['ssh',*SSH_OPTS,HOST,'test -f '+shlex.quote(remote_path)]
  probe=subprocess.run(probe_cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,check=False)
  entry={'remote':f'{HOST}:{remote_path}','probe_returncode':probe.returncode,'present':probe.returncode==0,'probe_stderr':probe.stderr}
  if probe.returncode==0:
   dest=local_capture/relative
   dest.parent.mkdir(parents=True,exist_ok=True)
   cp=subprocess.run(['scp',*SSH_OPTS,f'{HOST}:{remote_path}',str(dest)],check=False,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
   entry.update({'local':str(dest),'copy_returncode':cp.returncode,'copy_stderr':cp.stderr})
  collection.append(entry)
 for name in ['extract-command.json','charon.stdout.log','charon.stderr.log','gnu-time.txt','result.json','runner-status.json','early-failure.json','host-reservation-before.json','host-reservation-after.json']:
  collect_if_present(name)
 collect_if_present('R427RawMirCapture.llbc')
 output_copy=collection[-1]
 audit_rc=subprocess.run([sys.executable,str(HERE/'audit_saved_output.py'),'--baseline',str(R396_LLBC),'--stdout',str(local_capture/'charon.stdout.log'),'--output',str(local_capture/'R427RawMirCapture.llbc'),'--stderr',str(local_capture/'charon.stderr.log'),'--result',str(local_capture/'result.json'),'--gnu-time',str(local_capture/'gnu-time.txt'),'--host-before',str(local_capture/'host-reservation-before.json'),'--host-after',str(local_capture/'host-reservation-after.json'),'--launch-status',str(HERE/'launch-status.json'),'--build-receipt',str(HERE/'reviewed-build-receipt.snapshot.json'),'--report',str(local_capture/'saved-output-audit.json')],check=False).returncode
 (HERE/'collection-status.json').write_text(json.dumps({'ssh_returncode':ssh_result.returncode,'audit_returncode':audit_rc,'output_probe_returncode':output_copy['probe_returncode'],'output_present':output_copy['present'],'output_copy_returncode':output_copy.get('copy_returncode'),'collected_files':collection},indent=2)+'\n')
 return 0 if ssh_result.returncode==0 and audit_rc==0 else 2
if __name__=='__main__': raise SystemExit(main())
