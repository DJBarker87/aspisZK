import pathlib,json,traceback
try:
    import os,pathlib,hashlib,subprocess,json,shlex,shutil,re
    os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
    if os.environ.get('R440_ACTUAL_SOURCE_CAPTURE_ALLOW')!='1': raise SystemExit('capture gate closed; require explicit lead authorization')
    source_root=pathlib.Path("/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a")
    experiments=source_root/'docs/research/v8-no-work-100-20260907/experiments'
    workspace=experiments/'performance-host'
    root=pathlib.Path("/home/dombarker/project-offloads/aspis-r440-actual-mono-closure-20261003-a")
    root_preexisting=root.exists()
    root_created=False
    candidate_root=pathlib.Path("/home/dombarker/project-offloads/aspis-r440-mono-closure-binding-20261003-a")
    wrapper=candidate_root/'observer-bin/charon'
    driver=candidate_root/'observer-bin/charon-driver'
    original_wrapper=pathlib.Path("/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon")
    original_driver=pathlib.Path("/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon-driver")
    expected_candidate_main_sha="afc8d62e3b0097805f9688653a0e435d54ea65c5c8ba3e698eb46a4fd16c49f5"
    expected_candidate_closure_sha="93d29b0184be8503aafd8884f13f56eb73ea4f5eacdecb751bed5a28cc3fd5ed"
    expected_candidate_driver_sha="36cd66adb952d877a5ca6e17949fc4685525ed643d1b1fa7e92792d9a1d26625"
    candidate_overlay_paths={
        'main.rs':candidate_root/'charon/src/bin/charon-driver/main.rs',
        'translate_closures.rs':candidate_root/'charon/src/bin/charon-driver/translate/translate_closures.rs'
    }
    expected_candidate_overlays={'main.rs':expected_candidate_main_sha,'translate_closures.rs':expected_candidate_closure_sha}
    baseline=pathlib.Path("/home/dombarker/project-offloads/aspis-r429-actual-freeze-fold-20261003-c/R429ActualFreezeFold.llbc")
    r185_baseline=pathlib.Path("/home/dombarker/project-offloads/aspis-r185monomorphicfreeze-extract-20261002-a/R185MonomorphicFreeze.llbc")
    r437_comparison=pathlib.Path("/home/dombarker/project-offloads/aspis-r437-pointer-wrapper-layout-20261003-a/R437PointerWrapperLayout.llbc")
    rustc=pathlib.Path("/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc")
    expected={"r110_norm.rs":"8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e","circle_norm.rs":"3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2","line_norm.rs":"4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528","joined_inverse.rs":"ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb","aspis_core_field.rs":"639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499","performance_host_Cargo.toml":"62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c","performance_host_Cargo.lock":"a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814"}
    paths={"r110_norm.rs":experiments/'r110_norm.rs',"circle_norm.rs":experiments/'circle_norm.rs',"line_norm.rs":experiments/'line_norm.rs',"joined_inverse.rs":experiments/'joined_inverse.rs',"aspis_core_field.rs":source_root/'crates/aspis-core/src/field.rs',"performance_host_Cargo.toml":workspace/'Cargo.toml',"performance_host_Cargo.lock":workspace/'Cargo.lock'}
    def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
    def effective_cgroup():
        rel=next(line.split('::',1)[1].lstrip('/') for line in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
        cg=pathlib.Path('/sys/fs/cgroup')/rel
        names=['memory.high','memory.max','memory.swap.max','pids.max','memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events','pids.current']
        return {'path':str(cg),**{n:(cg/n).read_text().strip() if (cg/n).exists() else None for n in names}}
    std_expected={'/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter/macros.rs': '0ac47d295999ba8847d0df93557292fbad65d256db0c6521c396798d2e37677d', '/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter.rs': '83205f82241154964b1aecef87913ec92ce8c0b99285337c04e37840594f9251', '/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ptr/non_null.rs': 'adba64467653633cfa3fe0bbe6eec6f6d723221396b529c92d51eb9e39ba8cdd', '/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/mem/mod.rs': '9f450467849a7e829d2f57fe826518b7334df8a8eb206052d571ad7b5d018b9e'}
    std_before={k:sha(pathlib.Path(k)) for k in std_expected}
    assert std_before==std_expected
    paths['relation_callback.rs']=experiments/'relation_callback.rs'
    expected['relation_callback.rs']='4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f'
    actual={k:sha(v) for k,v in paths.items()}
    assert actual==expected,(actual,expected)
    overlays_before={k:sha(v) for k,v in candidate_overlay_paths.items()}
    assert overlays_before==expected_candidate_overlays,(overlays_before,expected_candidate_overlays)
    assert sha(baseline)=="c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465", "R429 pinned baseline changed"
    assert sha(r185_baseline)=="e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31", "R185 original source baseline changed"
    assert sha(r437_comparison)=="bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c", "R437 original-tool comparison LLBC changed"
    assert sha(wrapper)=="b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c", "candidate wrapper does not match reviewed unchanged wrapper"
    assert sha(driver)==expected_candidate_driver_sha, "candidate driver does not match R440 Bv2 receipt"
    assert sha(original_wrapper)=="b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c", "original wrapper changed"
    assert sha(original_driver)=="4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938", "original driver changed from pinned original toolchain"
    charon_toolchain=subprocess.check_output([str(wrapper),'toolchain-version'],text=True).strip()
    assert charon_toolchain=='nightly-2026-06-01',charon_toolchain
    charon_sysroot=subprocess.check_output([str(wrapper),'toolchain-path'],text=True).strip()
    rustc_version=subprocess.check_output([str(rustc),'-Vv'],text=True)
    assert "commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65" in rustc_version,rustc_version
    charon_source=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=charon_source,text=True).strip()=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c'
    assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=charon_source,text=True).strip()
    assert sha(charon_source/'charon/Cargo.lock')=='c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67'
    assert not root.exists(),f"capture root already exists: {root}"
    mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
    mem_total=int(mem['MemTotal'].split()[0])*1024; mem_avail=int(mem['MemAvailable'].split()[0])*1024
    candidate_max=7*1024**3; required=24*1024**3; safe=min(40*1024**3,mem_total-16*1024**3)
    assert mem_avail-candidate_max>=required,(mem,candidate_max,required)
    effective_before=effective_cgroup()
    assert (effective_before['memory.high'],effective_before['memory.max'],effective_before['memory.swap.max'],effective_before['pids.max'])==('5368709120','7516192768','0','128'),effective_before
    assert candidate_max<=safe,(candidate_max,safe)
    own_unit='aspis-r440-actual-mono-closure.service'
    active_aspis_units=[]; reserved_max=0; counted_cgroups=set()
    for manager in ('--user','--system'):
        listed=subprocess.check_output(['systemctl',manager,'list-units','--all','--plain','--no-legend'],text=True).splitlines()
        for line in listed:
            fields=line.split()
            if not fields: continue
            name=fields[0]
            if not name.startswith('aspis') or not name.endswith(('.service','.scope')) or name==own_unit: continue
            props=subprocess.check_output(['systemctl',manager,'show',name,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True)
            values=dict(x.split('=',1) for x in props.splitlines() if '=' in x)
            cgname=values.get('ControlGroup',''); cg=pathlib.Path('/sys/fs/cgroup')/cgname.lstrip('/')
            pids=[]
            if cgname and cg.exists():
                for f in cg.rglob('cgroup.procs'):
                    try: pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
                    except OSError: pass
            rawcap=values.get('MemoryMax',''); finite=rawcap.isdigit() and int(rawcap)>0
            if pids:
                assert finite,('uncapped active Aspis unit',manager,name,values)
                if cgname not in counted_cgroups:
                    reserved_max+=int(rawcap); counted_cgroups.add(cgname)
            active_aspis_units.append({'manager':manager,'unit':name,'control_group':cgname,'pids':pids,'MemoryMax_raw':rawcap,'MemoryMax_bytes':int(rawcap) if finite else None,'MemoryCurrent':values.get('MemoryCurrent')})
    assert candidate_max+reserved_max<=safe,(candidate_max,reserved_max,safe,active_aspis_units)
    heavy=[x.strip() for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if len(x.split())>1 and x.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')]
    assert not heavy,heavy
    root.mkdir()
    root_created=True
    fps=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
    flags=[json.loads(p.read_text())['rustflags'] for p in fps]
    assert flags and all(f==flags[0] for f in flags)
    expected_flags=['--cfg', 'v8_positive_transfer', '--cfg', 'v8_complete', '--cfg', 'v8_performance_fast', '--cfg', 'v8_structured', '--cfg', 'v8_fine_profile', '--cfg', 'v8_batch_m', '--cfg', 'v8_tower_batch', '--cfg', 'v8_query_kernels', '--cfg', 'v8_fused_rows', '--cfg', 'v8_shared_weights', '--cfg', 'v8_block_horner', '--cfg', 'v8_gamma_wrap', '--cfg', 'v8_reuse_gamma', '--cfg', 'v8_grouped_linear', '--cfg', 'v8_query_shared', '--cfg', 'v8_range_m31', '--cfg', 'v8_range_cm31', '--cfg', 'v8_sparse_groups', '--cfg', 'v8_range_dots', '--cfg', 'v8_cm_schoolbook', '--cfg', 'v8_prepared_schoolbook', '--cfg', 'v8_quiet_profile', '--cfg', 'v8_payment_extraction', '--cfg', 'v8_performance', '--cfg', 'v8_qm_hybrid', '--cfg', 'v8_qm_lazy_c0', '--cfg', 'v8_gamma_partial', '-A', 'dead_code', '-A', 'unexpected_cfgs', '--cfg', 'v8_circle_norm', '--cfg', 'v8_chord_norm', '--cfg', 'v8_joined_inverse', '--cfg', 'v8_split_inverse', '--cfg', 'v8_line_norm', '--cfg', 'v8_quotient_fused', '--cfg', 'v8_affine_primal', '--cfg', 'v8_compact_workspace', '--cfg', 'v8_gamma_fixed', '--cfg', 'v8_merkle_slices', '--cfg', 'v8_merkle_borrow', '--cfg', 'v8_leaf_record']
    assert flags[0]==expected_flags
    assert hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest()=="f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613"
    os.environ['RUSTFLAGS']=shlex.join(flags[0])
    command=[str(wrapper), 'cargo', '--preset', 'aeneas', '--mir', 'built', '--monomorphize', '--sysroot', 'default', '--start-from', 'crate::freeze', '--include', 'core::option', '--include', 'core::result::_::map_err', '--include', 'aspis_core::field', '--include', 'aspis_core::circle', '--include', 'aspis_core::transcript', '--include', 'core::iter::traits::iterator::Iterator::fold', '--include', 'core::slice::iter::_::fold', '--include', 'core::slice::iter::Iter', '--include', 'core::mem::SizedTypeProperties::IS_ZST', '--include', 'core::mem::SizedTypeProperties::SIZE', '--include', 'core::slice::_::iter', '--include', 'core::slice::iter::_::new', '--include', 'core::ptr::const_ptr::_::offset_from_unsigned::precondition_check', '--include', 'core::num::_::unchecked_add::precondition_check', '--include', 'core::ptr::non_null::NonNull', '--include', 'core::marker::PhantomData', '--dest-file', '/home/dombarker/project-offloads/aspis-r440-actual-mono-closure-20261003-a/R440ActualMonoClosure.llbc', '--', '--offline', '--locked', '--release', '--jobs', '1', '--features', 'insecure-spend-fixture,selected-v7-kernels', '--manifest-path', '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml', '--bin', 'aspis-v8-performance-host']
    assert '--print-original-ullbc' not in command
    assert sha(pathlib.Path('/home/dombarker/project-offloads/aspis-r429-actual-freeze-fold-20261003-c/R429ActualFreezeFold.llbc'))=='c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465'
    baseline_before=sha(baseline); r185_before=sha(r185_baseline); r437_before=sha(r437_comparison)
    record={'stdlib_hashes_before':std_before,'source_hashes_before':actual,'baseline_sha_before':baseline_before,'r185_source_baseline_sha_before':r185_before,'r437_comparison_sha_before':r437_before,'wrapper_sha256':sha(wrapper),'driver_sha256':sha(driver),'original_wrapper_sha256':sha(original_wrapper),'original_driver_sha256':sha(original_driver),'candidate_overlay_hashes_before':overlays_before,'candidate_driver_sha256':sha(driver),'rustflags_sha256':"f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613",'rustflags':flags[0],'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'host_meminfo_before':mem,'effective_cgroup_before':effective_before,'active_aspis_units_both_managers':active_aspis_units,'deduplicated_reserved_memory_max_bytes':reserved_max,'candidate_memory_max_bytes':candidate_max,'safe_working_limit_bytes':safe,'heavy_processes':heavy,'base_extract_command_sha256':'2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96','launch_revision':'3b9e8d7f0122e6dc966a809904adbd722ae3079d'}
    (root/'host-reservation-before.json').write_text(json.dumps(record,indent=2))
    (root/'extract-command.json').write_text(json.dumps({'command':command,'start_from':['crate::freeze'],'include':[command[i+1] for i,x in enumerate(command) if x=='--include'],'features':'insecure-spend-fixture,selected-v7-kernels','monomorphize':True,'environment':{},'source_hashes':actual,'baseline_sha256':sha(baseline),'base_extract_command_sha256':'2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96'},indent=2))
    with (root/'charon.stdout.log').open('wb') as so, (root/'charon.stderr.log').open('wb') as se:
     run=subprocess.run(['/usr/bin/time','-v','-o',str(root/'gnu-time.txt'),*command],stdout=so,stderr=se)
    source_after={k:sha(v) for k,v in paths.items()}
    overlays_after={k:sha(v) for k,v in candidate_overlay_paths.items()}
    baseline_after=sha(baseline); r185_after=sha(r185_baseline); r437_after=sha(r437_comparison)
    std_after={k:sha(pathlib.Path(k)) for k in std_expected}
    assert std_after==std_expected
    (root/'host-reservation-after.json').write_text(json.dumps({'stdlib_hashes_after':std_after,'source_hashes_after':source_after,'baseline_sha_after':baseline_after,'r185_source_baseline_sha_after':r185_after,'r437_comparison_sha_after':r437_after,'host_meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'effective_cgroup_after':effective_cgroup(),'rustc_version_verbose':rustc_version,'candidate_overlay_hashes_after':overlays_after,'candidate_wrapper_sha256_after':sha(wrapper),'candidate_driver_sha256_after':sha(driver),'original_wrapper_sha256_after':sha(original_wrapper),'original_driver_sha256_after':sha(original_driver)},indent=2))
    assert source_after==expected,source_after
    assert overlays_after==expected_candidate_overlays,(overlays_after,expected_candidate_overlays)
    assert sha(wrapper)=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c' and sha(driver)==expected_candidate_driver_sha
    assert sha(original_wrapper)=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c' and sha(original_driver)=='4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938'
    assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=charon_source,text=True).strip()
    assert baseline_after=="c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465",baseline_after
    assert r185_after==r185_before=="e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31",(r185_before,r185_after)
    assert r437_after==r437_before=="bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c",(r437_before,r437_after)
    llbc=root/'R440ActualMonoClosure.llbc'
    gtxt=(root/'gnu-time.txt').read_text()
    def metric(pattern):
     m=re.search(pattern,gtxt,re.M); return m.group(1).strip() if m else None
    result={'charon_exit_status':run.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'), 'peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0), 'swap_count':int(metric(r'Swaps:\s*(\d+)') or 0), 'gnu_time_exit_status':int(metric(r'Exit status:\s*(\d+)') or -1),'llbc_exists':llbc.is_file(),'llbc_sha256':sha(llbc) if llbc.is_file() else None,'charon_stdout_sha256':sha(root/'charon.stdout.log'),'charon_stdout_bytes':(root/'charon.stdout.log').stat().st_size,'charon_stderr_sha256':sha(root/'charon.stderr.log'),'charon_stderr_bytes':(root/'charon.stderr.log').stat().st_size,'original_driver_sha256':sha(original_driver),'candidate_driver_sha256':sha(driver),'base_extract_command_sha256':'2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96','candidate_get_mir_sha256':'N/A; no get_mir observation hook; two-file Bv2 tool patch','reviewed_patch_sha256':'6208cbcd139815ed783ca83952fef7a539c89596156636c2ee7c283260ae9ad8','source_commit':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','candidate_b_patch_sha256':'6208cbcd139815ed783ca83952fef7a539c89596156636c2ee7c283260ae9ad8','candidate_overlay_hashes_before_after':{'before':overlays_before,'after':overlays_after},'baseline_sha256_before_after':[baseline_before,baseline_after],'r185_source_baseline_sha256_before_after':[r185_before,r185_after],'r437_comparison_sha256_before_after':[r437_before,r437_after],'source_hashes_before_after':{'before':actual,'after':source_after},'source_revision_recorded':'3b9e8d7f0122e6dc966a809904adbd722ae3079d','capture_revision':'3b9e8d7f0122e6dc966a809904adbd722ae3079d','requested_root':'crate::freeze','has_errors':json.loads(llbc.read_text()).get('has_errors') if llbc.is_file() else None,'rustc_version_verbose':rustc_version,'charon_toolchain':charon_toolchain,'charon_sysroot':charon_sysroot,'formal_axioms':'N/A; diagnostic LLBC only; native extraction, no Lean theorem'}
    (root/'result.json').write_text(json.dumps(result,indent=2))
    print('R440_CHILD_EXIT',run.returncode)
    raise SystemExit(run.returncode)

except BaseException as exc:
    if 'root' in globals() and not root_preexisting:
        root.mkdir(parents=True,exist_ok=True)
        (root/'runner-status.json').write_text(json.dumps({'status':'terminal','code':getattr(exc,'code',None),'failure':repr(exc),'traceback':traceback.format_exc(),'effective_cgroup':globals().get('effective_before')},indent=2))
    raise
