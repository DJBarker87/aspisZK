import pathlib,json,traceback
try:
    import os,pathlib,hashlib,subprocess,json,shlex,shutil,re
    os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
    source_root=pathlib.Path("/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a")
    experiments=source_root/'docs/research/v8-no-work-100-20260907/experiments'
    workspace=experiments/'performance-host'
    candidate=pathlib.Path("/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a")
    root=pathlib.Path("/home/dombarker/project-offloads/aspis-r427-raw-mir-capture-20261003-b")
    root_preexisting=root.exists()
    root_created=False
    wrapper=pathlib.Path("/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a/observer-bin/charon")
    driver=pathlib.Path("/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a/observer-bin/charon-driver")
    original_wrapper=pathlib.Path("/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon")
    original_driver=pathlib.Path("/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon-driver")
    baseline=pathlib.Path("/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc")
    rustc=pathlib.Path("/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc")
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
    assert sha(baseline)=="399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae", "R396 baseline changed"
    assert sha(wrapper)=="b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c", "candidate wrapper does not match reviewed unchanged wrapper"
    assert sha(driver)=="a7911f86aa775e99e685cc7d1c09e894e6e30c07dc65e83dd21ac0555ef08318", "candidate driver does not match reviewed build receipt"
    assert sha(original_wrapper)=="b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c", "original wrapper changed"
    assert sha(original_driver)=="4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938", "original driver changed from R396 toolchain pin"
    charon_toolchain=subprocess.check_output([str(wrapper),'toolchain-version'],text=True).strip()
    assert charon_toolchain=='nightly-2026-06-01',charon_toolchain
    charon_sysroot=subprocess.check_output([str(wrapper),'toolchain-path'],text=True).strip()
    rustc_version=subprocess.check_output([str(rustc),'-Vv'],text=True)
    assert "commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65" in rustc_version,rustc_version
    assert sha(candidate/'charon/Cargo.lock')=="c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67", "candidate Charon Cargo.lock differs from pinned source"
    assert sha(candidate/'charon/src/bin/charon-driver/translate/get_mir.rs')=="246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab", "candidate hook source differs from reviewed build receipt"
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
    active_services=subprocess.check_output(['systemctl','--user','list-units','--all','--plain','--state=running','--no-legend'],text=True)
    other_active_aspis=[line.strip() for line in active_services.splitlines() if line.split() and line.split()[0].startswith('aspis') and line.split()[0].endswith(('.service','.scope')) and line.split()[0]!='aspis-r427-raw-mir-capture.service']
    assert not other_active_aspis,other_active_aspis
    heavy=[x.strip() for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if len(x.split())>1 and x.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')]
    assert not heavy,heavy
    assert sha(candidate/'charon/Cargo.lock')=="c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67", "candidate locked toolchain inputs differ from reviewed pinned source"
    root.mkdir()
    root_created=True
    (root/'preserved-original-binaries').mkdir()
    shutil.copy2(original_wrapper,root/'preserved-original-binaries/charon-wrapper')
    shutil.copy2(original_driver,root/'preserved-original-binaries/charon-driver')
    assert sha(root/'preserved-original-binaries/charon-wrapper')=="b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c"
    assert sha(root/'preserved-original-binaries/charon-driver')=="4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938"
    fps=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
    flags=[json.loads(p.read_text())['rustflags'] for p in fps]
    assert flags and all(f==flags[0] for f in flags)
    expected_flags=['--cfg', 'v8_positive_transfer', '--cfg', 'v8_complete', '--cfg', 'v8_performance_fast', '--cfg', 'v8_structured', '--cfg', 'v8_fine_profile', '--cfg', 'v8_batch_m', '--cfg', 'v8_tower_batch', '--cfg', 'v8_query_kernels', '--cfg', 'v8_fused_rows', '--cfg', 'v8_shared_weights', '--cfg', 'v8_block_horner', '--cfg', 'v8_gamma_wrap', '--cfg', 'v8_reuse_gamma', '--cfg', 'v8_grouped_linear', '--cfg', 'v8_query_shared', '--cfg', 'v8_range_m31', '--cfg', 'v8_range_cm31', '--cfg', 'v8_sparse_groups', '--cfg', 'v8_range_dots', '--cfg', 'v8_cm_schoolbook', '--cfg', 'v8_prepared_schoolbook', '--cfg', 'v8_quiet_profile', '--cfg', 'v8_payment_extraction', '--cfg', 'v8_performance', '--cfg', 'v8_qm_hybrid', '--cfg', 'v8_qm_lazy_c0', '--cfg', 'v8_gamma_partial', '-A', 'dead_code', '-A', 'unexpected_cfgs', '--cfg', 'v8_circle_norm', '--cfg', 'v8_chord_norm', '--cfg', 'v8_joined_inverse', '--cfg', 'v8_split_inverse', '--cfg', 'v8_line_norm', '--cfg', 'v8_quotient_fused', '--cfg', 'v8_affine_primal', '--cfg', 'v8_compact_workspace', '--cfg', 'v8_gamma_fixed', '--cfg', 'v8_merkle_slices', '--cfg', 'v8_merkle_borrow', '--cfg', 'v8_leaf_record']
    assert flags[0]==expected_flags
    assert hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest()=="f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613"
    os.environ['RUSTFLAGS']=shlex.join(flags[0])
    command=[str(wrapper),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
    for inc in ["core::option", "aspis_core::field", "core::iter::adapters::chain::Chain", "core::iter::adapters::chain::_::next", "core::iter::adapters::chain::_::try_fold", "core::iter::traits::iterator::Iterator::any", "core::iter::traits::iterator::Iterator::chain", "core::slice::iter::_::any", "core::slice::_::last", "core::iter::traits::iterator::Iterator::try_fold", "core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch", "core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output", "core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual"]: command.extend(['--include',inc])
    command += ['--dest-file',str(root/'R427RawMirCapture.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(workspace/'Cargo.toml'),'--bin','aspis-v8-performance-host']
    assert '--print-original-ullbc' not in command
    baseline_before=sha(baseline)
    record={'source_hashes_before':actual,'baseline_sha_before':baseline_before,'wrapper_sha256':sha(wrapper),'driver_sha256':sha(driver),'candidate_driver_sha256':sha(driver),'rustflags_sha256':"f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613",'rustflags':flags[0],'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'host_meminfo_before':mem,'effective_cgroup_before':effective_before,'existing_aspis_slices':slices,'active_slice_memory_max_bytes':active_slice_memory_max,'candidate_memory_max_bytes':candidate_max,'safe_working_limit_bytes':safe,'other_active_aspis_services':other_active_aspis,'heavy_processes':heavy,'reviewed_build_receipt_sha256':'42969fee8400f8cf5c5a96099fb39266752258a4dc78a1e551502b2583f42e64','launch_revision':'a6cdbfac929ee3afe75b42382f08370216664145'}
    (root/'host-reservation-before.json').write_text(json.dumps(record,indent=2))
    (root/'extract-command.json').write_text(json.dumps({'command':command,'start_from':["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"],'include':["core::option", "aspis_core::field", "core::iter::adapters::chain::Chain", "core::iter::adapters::chain::_::next", "core::iter::adapters::chain::_::try_fold", "core::iter::traits::iterator::Iterator::any", "core::iter::traits::iterator::Iterator::chain", "core::slice::iter::_::any", "core::slice::_::last", "core::iter::traits::iterator::Iterator::try_fold", "core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch", "core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output", "core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual"],'features':'insecure-spend-fixture,selected-v7-kernels','monomorphize':False,'environment':{'ASPIS_R427_OBSERVE_MIR':'1'},'source_hashes':actual,'baseline_sha256':sha(baseline),'reviewed_build_receipt_sha256':'42969fee8400f8cf5c5a96099fb39266752258a4dc78a1e551502b2583f42e64'},indent=2))
    # Raw observer is opt-in and diagnostics only; no --print-original-ullbc option is added.
    os.environ['ASPIS_R427_OBSERVE_MIR']='1'
    with (root/'charon.stdout.log').open('wb') as so, (root/'charon.stderr.log').open('wb') as se:
     run=subprocess.run(['/usr/bin/time','-v','-o',str(root/'gnu-time.txt'),*command],stdout=so,stderr=se)
    source_after={k:sha(v) for k,v in paths.items()}
    baseline_after=sha(baseline)
    (root/'host-reservation-after.json').write_text(json.dumps({'source_hashes_after':source_after,'baseline_sha_after':baseline_after,'host_meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'effective_cgroup_after':effective_cgroup(),'rustc_version_verbose':rustc_version},indent=2))
    assert source_after==expected,source_after
    assert baseline_after=="399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae",baseline_after
    llbc=root/'R427RawMirCapture.llbc'
    gtxt=(root/'gnu-time.txt').read_text()
    def metric(pattern):
     m=re.search(pattern,gtxt,re.M); return m.group(1).strip() if m else None
    result={'charon_exit_status':run.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'), 'peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0), 'swap_count':int(metric(r'Swaps:\s*(\d+)') or 0), 'gnu_time_exit_status':int(metric(r'Exit status:\s*(\d+)') or -1),'llbc_exists':llbc.is_file(),'llbc_sha256':sha(llbc) if llbc.is_file() else None,'observer_stdout_sha256':sha(root/'charon.stdout.log'),'observer_stdout_bytes':(root/'charon.stdout.log').stat().st_size,'observer_stderr_sha256':sha(root/'charon.stderr.log'),'observer_stderr_bytes':(root/'charon.stderr.log').stat().st_size,'candidate_driver_sha256':sha(driver),'reviewed_build_receipt_sha256':'42969fee8400f8cf5c5a96099fb39266752258a4dc78a1e551502b2583f42e64','candidate_get_mir_sha256':'246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab','reviewed_patch_sha256':'7fa5f30e64b12528a01bbfc792dbda8e457e3502fa445be9cdc4db6c3430d174','source_commit':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','baseline_sha256_before_after':[baseline_before,baseline_after],'source_hashes_before_after':{'before':actual,'after':source_after},'source_revision_recorded':'13617a70553ed3c43cee312acba2407b29a7052d','capture_revision':'a6cdbfac929ee3afe75b42382f08370216664145','requested_root':'crate::circle_norm::joined_inverse::line_norm::r110_norm::batch','has_errors':json.loads(llbc.read_text()).get('has_errors') if llbc.is_file() else None,'rustc_version_verbose':rustc_version,'charon_toolchain':charon_toolchain,'charon_sysroot':charon_sysroot,'frame_marker_counts':{k:root.joinpath('charon.stderr.log').read_text(errors='replace').count(k) for k in ['ASPIS_R427_RAW_MIR_BEGIN','ASPIS_R427_RAW_MIR_END','ASPIS_R427_STATEMENT_SOURCE','ASPIS_R427_USE_RETAG','ASPIS_R427_TERMINATOR_SOURCE','ASPIS_R427_CALL_ARG']},'formal_axioms':'N/A; diagnostic LLBC only'}
    (root/'result.json').write_text(json.dumps(result,indent=2))
    print('R427_CHILD_EXIT',run.returncode)
    raise SystemExit(run.returncode)

except SystemExit as exc:
    if 'root' in globals() and not root_preexisting:
        root.mkdir(parents=True,exist_ok=True)
        details={'status':'SystemExit','code':exc.code,'traceback':traceback.format_exc(),'source_hashes_before':globals().get('actual'),'source_hashes_after':globals().get('source_after'),'baseline_before':globals().get('baseline_before'),'baseline_after':globals().get('baseline_after'),'effective_cgroup':globals().get('effective_before'),'formal_axioms':'N/A; diagnostic only'}
        (root/'runner-status.json').write_text(json.dumps(details,indent=2))
    raise
except BaseException as exc:
    if 'root' in globals() and not root_preexisting:
        root.mkdir(parents=True,exist_ok=True)
        details={'status':'exception','failure':repr(exc),'traceback':traceback.format_exc(),'source_hashes_before':globals().get('actual'),'source_hashes_after':globals().get('source_after'),'baseline_before':globals().get('baseline_before'),'baseline_after':globals().get('baseline_after'),'effective_cgroup':globals().get('effective_before'),'formal_axioms':'N/A; diagnostic only'}
        (root/'early-failure.json').write_text(json.dumps(details,indent=2))
    raise
