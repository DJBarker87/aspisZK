#!/usr/bin/env python3
"""Read-only R427 diagnostic audit. Never launches extraction or a compiler."""
import argparse, copy, hashlib, json, pathlib, re, sys
p=argparse.ArgumentParser()
for name in ('baseline','stdout','output','stderr','result','gnu-time','host-before','host-after','launch-status','build-receipt','report'):
    p.add_argument('--'+name,type=pathlib.Path,required=True)
a=p.parse_args()
BASE_EXPECTED='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
RUSTC_COMMIT='14210df0e27ccd7d9e6a05b8085cbd438e4bbc65'
TARGET='core::iter::traits::iterator::Iterator::try_fold'
SOURCES={'r110_norm.rs':'8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e','circle_norm.rs':'3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2','line_norm.rs':'4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528','joined_inverse.rs':'ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb','aspis_core_field.rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499','performance_host_Cargo.toml':'62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c','performance_host_Cargo.lock':'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814'}
fail=[]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path,label):
    try: return json.loads(path.read_text())
    except Exception as exc:
        fail.append(f'{label} unavailable or invalid: {exc!r}')
        return {}
def cgroup_values(snapshot):
    if not isinstance(snapshot,dict): return None
    return tuple(snapshot.get(k) for k in ('memory.high','memory.max','memory.swap.max','pids.max'))
def keyed(rows):
    mapping={}; dups=[]
    for i,row in enumerate(rows):
        k=json.dumps(row['key'],sort_keys=True,separators=(',',':'),ensure_ascii=False)
        if k in mapping: dups.append(i)
        mapping[k]=row['value']
    return mapping,dups
missing=[str(path) for path in (a.baseline,a.stdout,a.output,a.stderr,a.result,a.gnu_time,a.host_before,a.host_after,a.launch_status,a.build_receipt) if not path.is_file()]
if missing:
    fail.extend('required saved output missing: '+x for x in missing)
old=load(a.baseline,'baseline') if a.baseline.exists() else {}
new=load(a.output,'output') if a.output.exists() else {}
r=load(a.result,'result') if a.result.exists() else {}
before=load(a.host_before,'host-before') if a.host_before.exists() else {}
after=load(a.host_after,'host-after') if a.host_after.exists() else {}
launch=load(a.launch_status,'launch-status') if a.launch_status.exists() else {}
build=load(a.build_receipt,'reviewed-build-receipt') if a.build_receipt.exists() else {}
gnu=a.gnu_time.read_text(errors='replace') if a.gnu_time.exists() else ''
stderr=a.stderr.read_text(errors='replace') if a.stderr.exists() else ''
def gv(pattern):
    m=re.search(pattern,gnu,re.M); return m.group(1).strip() if m else None
wall=gv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)')
rss=gv(r'Maximum resident set size \(kbytes\):\s*(\d+)')
swaps=gv(r'Swaps:\s*(\d+)')
gnu_status=gv(r'Exit status:\s*(\d+)')
if a.baseline.exists() and sha(a.baseline)!=BASE_EXPECTED: fail.append('R396 baseline SHA differs from pin')
differences={}; sn_ok=rest_ok=False
try:
    if old and new:
        old_trans=old.get('translated'); new_trans=new.get('translated')
        if not isinstance(old_trans,dict) or not isinstance(new_trans,dict): raise ValueError('translated object missing')
        old_opts=old_trans.get('options'); new_opts=new_trans.get('options')
        if not isinstance(old_opts,dict) or not isinstance(new_opts,dict): raise ValueError('options object missing')
        differences={k:(old_opts.get(k),new_opts.get(k)) for k in set(old_opts)|set(new_opts) if old_opts.get(k)!=new_opts.get(k)}
        if set(differences)!={'dest_file'}: fail.append('translated.options differs outside dest_file')
        if old_opts.get('print_original_ullbc') is not False or new_opts.get('print_original_ullbc') is not False: fail.append('print_original_ullbc is not false')
        dest='/home/dombarker/project-offloads/aspis-r427-raw-mir-capture-20261003-b/R427RawMirCapture.llbc'
        if new_opts.get('dest_file')!=dest: fail.append('wrong exact fresh dest_file')
        old_sn=old_trans.get('short_names'); new_sn=new_trans.get('short_names')
        if not isinstance(old_sn,list) or not isinstance(new_sn,list): raise ValueError('short_names arrays missing')
        normalized=copy.deepcopy(new)
        normalized['translated']['options']['dest_file']=old_opts.get('dest_file')
        om,od=keyed(old_sn); nm,nd=keyed(new_sn)
        sn_ok=len(old_sn)==len(new_sn)==347 and not od and not nd and om==nm
        if not sn_ok: fail.append('short_names not an exact unique 347-entry map modulo order')
        normalized['translated']['short_names']=old_sn
        rest_ok=normalized==old
        if not rest_ok: fail.append('decoded native LLBC differs outside allowed dest_file/map ordering')
    else: fail.append('baseline or output LLBC JSON is unavailable')
except Exception as exc:
    fail.append(f'LLBC structural comparison could not complete: {exc!r}')
if gnu_status is None or rss is None or swaps is None or wall is None: fail.append('GNU time receipt incomplete')
if int(gnu_status or -1)!=r.get('charon_exit_status') or int(gnu_status or -1)!=r.get('gnu_time_exit_status'): fail.append('GNU time and child result statuses disagree')
if (wall!=r.get('wall_time') or int(rss or -1)!=r.get('peak_rss_kib') or int(swaps or -1)!=r.get('swap_count')): fail.append('GNU time wall/RSS/swap does not match result.json')
if int(swaps or -1)!=0: fail.append('GNU time reports nonzero swap use')
if r.get('charon_exit_status')!=0: fail.append('Charon child failed')
if r.get('has_errors') is not False or (new and new.get('has_errors') is not False): fail.append('LLBC has_errors is not false')
if r.get('llbc_sha256')!=(sha(a.output) if a.output.exists() else None): fail.append('output LLBC checksum differs from result receipt')
if r.get('observer_stdout_sha256')!=(sha(a.stdout) if a.stdout.exists() else None): fail.append('stdout checksum differs from result receipt')
if r.get('observer_stdout_bytes')!=(a.stdout.stat().st_size if a.stdout.exists() else None): fail.append('stdout byte count differs from result receipt')
if r.get('observer_stderr_sha256')!=(sha(a.stderr) if a.stderr.exists() else None): fail.append('stderr checksum differs from result receipt')
if r.get('observer_stderr_bytes')!=(a.stderr.stat().st_size if a.stderr.exists() else None): fail.append('stderr byte count differs from result receipt')
if r.get('source_hashes_before_after',{}).get('before')!=SOURCES or r.get('source_hashes_before_after',{}).get('after')!=SOURCES or after.get('source_hashes_after')!=SOURCES: fail.append('seven frozen source hashes are not pinned before/after')
if r.get('baseline_sha256_before_after')!=[BASE_EXPECTED,BASE_EXPECTED] or after.get('baseline_sha_after')!=BASE_EXPECTED: fail.append('R396 baseline changed during run')
if r.get('source_revision_recorded')!='13617a70553ed3c43cee312acba2407b29a7052d': fail.append('unexpected frozen-source revision record')
if r.get('capture_revision')!=launch.get('launch_revision'): fail.append('capture and launch revision receipts disagree')
if launch.get('ssh_returncode')!=0: fail.append('SSH/systemd-run returned nonzero')
if r.get('reviewed_build_receipt_sha256')!=launch.get('build_receipt_sha256'): fail.append('run receipt differs from reviewed build-receipt SHA')
if a.build_receipt.exists() and sha(a.build_receipt)!=launch.get('build_receipt_sha256'): fail.append('saved build receipt SHA differs from launch receipt')
for key,value in {'candidate_root':'/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a','wrapper_path':'/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a/observer-bin/charon','driver_path':'/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a/observer-bin/charon-driver','wrapper_sha256':'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','original_driver_sha256':'4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938','charon_lock_sha256':'c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67','candidate_get_mir_sha256':'246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab','build_exit_status':0,'rustc_commit':RUSTC_COMMIT,'source_commit':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','reviewed':True}.items():
    if build.get(key)!=value or launch.get(key)!=value: fail.append(f'build receipt binding mismatch for {key}')
for key in ('driver_sha256','candidate_get_mir_sha256','reviewed_patch_sha256'):
    if not isinstance(build.get(key),str) or not re.fullmatch(r'[0-9a-f]{64}',build[key]) or launch.get(key)!=build.get(key): fail.append(f'build receipt SHA binding missing/mismatched for {key}')
if r.get('candidate_driver_sha256')!=launch.get('candidate_driver_sha256'): fail.append('candidate driver hash differs from launch/build receipt')
for key in ('candidate_root','candidate_get_mir_sha256','reviewed_patch_sha256','source_commit','rustc_commit'):
    if launch.get(key) in (None,''): fail.append('launch status lacks build binding '+key)
if launch.get('candidate_root')!='/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a': fail.append('launch status candidate root differs from pinned root')
expected_effective=('5368709120','7516192768','0','128')
cb=before.get('effective_cgroup_before',{}); ca=after.get('effective_cgroup_after',{})
if cgroup_values(before.get('effective_cgroup_before'))!=expected_effective: fail.append('actual preflight process cgroup caps differ from required 5G/7G/0/128')
if cgroup_values(after.get('effective_cgroup_after'))!=expected_effective: fail.append('actual post-run process cgroup caps differ from required 5G/7G/0/128')
if cb.get('path')!=ca.get('path'): fail.append('actual cgroup path changed during run')
try:
    if int(ca.get('memory.peak','-1'))>7516192768: fail.append('effective cgroup memory peak exceeds 7 GiB')
except Exception: fail.append('effective cgroup memory peak missing/invalid')
if not r.get('rustc_version_verbose') or f'commit-hash: {RUSTC_COMMIT}' not in r.get('rustc_version_verbose',''): fail.append('runtime rustc -Vv commit does not match pinned R396 toolchain')
if r.get('charon_toolchain')!='nightly-2026-06-01': fail.append('wrapper-reported Charon toolchain differs from R396 pin')
if r.get('charon_sysroot')!='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu': fail.append('wrapper-reported sysroot differs from R396 pin')
if cb.get('memory.events') is None or ca.get('memory.events') is None: fail.append('actual cgroup memory.events evidence missing')
for label,cg in [('before',cb),('after',ca)]:
    if cg.get('memory.swap.current')!='0' or cg.get('memory.swap.peak')!='0': fail.append(f'{label} actual cgroup swap counters are not zero')
    try: events=dict(line.split() for line in cg.get('memory.events','').splitlines()); oom=int(events.get('oom','-1')); oom_kill=int(events.get('oom_kill','-1'))
    except Exception: oom=oom_kill=-1
    if oom!=0 or oom_kill!=0: fail.append(f'{label} actual cgroup OOM event counters are not zero')
if r.get('candidate_driver_sha256') is None: fail.append('result receipt omits candidate driver hash')
begins=list(re.finditer(r'^ASPIS_R427_RAW_MIR_BEGIN name=([^\s]+) def_id=([^\n]+)$',stderr,re.M)); ends=list(re.finditer(r'^ASPIS_R427_RAW_MIR_END name=([^\s]+) def_id=([^\n]+)$',stderr,re.M))
frame=None; frame_errors=[]
if len(begins)==len(ends)==1:
    b,e=begins[0],ends[0]
    if b.start()>=e.start() or b.group(1)!=TARGET or e.group(1)!=TARGET or b.group(2)!=e.group(2): frame_errors.append('frame label/order/DefId mismatch')
    else: frame=stderr[b.start():e.end()]
else: frame_errors.append(f'expected one selected frame, got begin={len(begins)} end={len(ends)}')
for marker in ('ASPIS_R427_STATEMENT_SOURCE','ASPIS_R427_USE_RETAG','ASPIS_R427_TERMINATOR_SOURCE','ASPIS_R427_CALL_ARG'):
    if frame is None or marker not in frame: frame_errors.append('frame missing '+marker)
fail.extend(frame_errors)
a.report.parent.mkdir(parents=True,exist_ok=True)
if frame is not None: (a.report.parent/'mir-frame.txt').write_text(frame+'\n')
report={'classification':'saved-output diagnostic audit only; no extraction/compiler/Lean run','metrics':{'wall_time':wall,'peak_rss_kib':int(rss) if rss else None,'swap_count':int(swaps) if swaps else None,'gnu_time_exit_status':int(gnu_status) if gnu_status else None,'result_exit_status':r.get('charon_exit_status'),'actual_cgroup_before':before.get('effective_cgroup_before'),'actual_cgroup_after':after.get('effective_cgroup_after'),'runtime_rustc':r.get('rustc_version_verbose')},'receipts':{'result_sha256':sha(a.result) if a.result.exists() else None,'build_receipt_sha256':sha(a.build_receipt) if a.build_receipt.exists() else None,'stdout_sha256':sha(a.stdout) if a.stdout.exists() else None,'stderr_sha256':sha(a.stderr) if a.stderr.exists() else None,'output_sha256':sha(a.output) if a.output.exists() else None,'launch_status':launch},'llbc_gate':{'option_differences':differences,'short_names_map_exact':sn_ok,'all_other_fields_exact':rest_ok},'raw_frame':{'target':TARGET,'begin_count':len(begins),'end_count':len(ends),'frame_errors':frame_errors,'saved_full_frame':'mir-frame.txt' if frame is not None else None},'passed':not fail,'failures':fail,'boundary':'Equality and raw MIR observation inventory only. It does not prove MIR Copy/Retag source correspondence, callback semantics, or a source theorem.'}
a.report.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':report['passed'],'failures':fail,'report':str(a.report)},indent=2))
sys.exit(0 if not fail else 2)
