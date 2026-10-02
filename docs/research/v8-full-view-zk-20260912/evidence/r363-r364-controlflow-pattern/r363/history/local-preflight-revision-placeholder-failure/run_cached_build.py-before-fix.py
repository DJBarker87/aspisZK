#!/usr/bin/env python3
# Launch-capable candidate runner. The root launcher injects the captured Git HEAD.
# Do not execute before lead review and launch authorization.
import hashlib, json, pathlib, subprocess, time

root = pathlib.Path('/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a')
src = root / 'src'
source_audit = root / 'candidate-audit'
audit = source_audit / 'r363-build'
parent = pathlib.Path('/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a')
launch_revision = '7c588ebcd62955448a0298b3d480aa7e23c408bb'
source_revision = '56a931fc3879354a2fa584e73bd0a1d412714851'
parent_launch_revision = '078a3bd7d4471a5f10549843e7818b956163bb77'
image_id = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
expected_manifest_sha = 'e43845424aeb6964281bd0d5e9d7ba4beb3d0a0aefe10b8acdab382127503e89'
expected_tree_sha = 'ecba5557e6d92687aca0d2f89bb15426b88cdf5fceca25a27eca497c1d73fa37'
expected_clone_sha = '7b0482d1ea4b068ece18267002cdcd7dd24689f18b6909e2964cbe6bb5bba275'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

# Validate the saved two-file overlay audit without rerunning its tree/inode writer.
assert sha(source_audit / 'clone-audit.json') == expected_clone_sha
clone = json.loads((source_audit / 'clone-audit.json').read_text())
assert clone['status'] == 'candidate source overlay prepared only; not built or translated'
assert clone['changed_source_paths_vs_R360'] == ['src/NameMatcher.ml', 'src/llbc/LlbcAstUtils.ml']
assert clone['only_requested_overlay_files_changed'] is True
assert clone['shared_regular_file_inodes'] == 0
assert clone['R360_nonbuild_sources_match_saved_manifest'] is True
assert clone['cached_binary_unchanged'] is True
assert clone['R360_cached_binary_sha256'] == '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416'
assert clone['R363_cached_binary_sha256'] == clone['R360_cached_binary_sha256']
assert clone['R363_canonical_tree_sha256'] == expected_tree_sha
assert clone['R363_tree_manifest_sha256'] == expected_manifest_sha
assert clone['source_hashes']['R363_NameMatcher_ml_sha256'] == 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8'
assert clone['source_hashes']['R363_LlbcAstUtils_ml_sha256'] == '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97'
assert sha(source_audit / 'R363-source-tree-manifest.json') == expected_manifest_sha
assert src.is_dir() and (src / '_build/default/main.exe').is_file()
assert not (root / 'aeneas-r363-instantiated-pattern-candidate').exists()
assert sha(src / 'NameMatcher.ml') == 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8'
assert sha(src / 'llbc/LlbcAstUtils.ml') == '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97'
assert sha(src / 'extract/ExtractTypes.ml') == '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527'
assert sha(src / 'TranslateCore.ml') == '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9'
assert sha(src / 'interp/InterpExpansion.ml') == 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19'
assert sha(src / 'PrePasses.ml') == '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
assert sha(src / '_build/default/main.exe') == '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416'
assert sha(parent / 'aeneas-r360-comment-context-candidate') == '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416'
assert audit.is_dir() and sorted(p.name for p in audit.iterdir()) == ['run_cached_build.py'], sorted(p.name for p in audit.iterdir()) if audit.exists() else 'missing r363-build directory'

image = subprocess.check_output(['docker', 'image', 'inspect', 'ef96e46342a4', '--format', '{{.Id}} {{.Size}}'], text=True).strip()
assert image.startswith(image_id + ' '), image
existing = subprocess.check_output(['docker', 'ps', '-a', '--filter', 'name=aspis-r363-instantiated-pattern-build', '--format', '{{.ID}} {{.Names}}'], text=True).strip()
assert not existing, existing
mem = lambda: {k: v for k, v in (line.split(':', 1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree')}
before = mem()
available_kib = int(before['MemAvailable'].split()[0])
assert available_kib >= 24 * 1024 * 1024, before
r360_parent_slice = subprocess.check_output(['systemctl', 'show', 'aspisr360.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'MemoryCurrent'], text=True)
active_services = subprocess.check_output(['systemctl', '--user', 'list-units', '--type=service', '--state=running', '--no-legend'], text=True)
docker_before = subprocess.check_output(['docker', 'ps', '--no-trunc', '--format', '{{.ID}} {{.Names}} {{.Status}}'], text=True)
pre = {
    'meminfo_before': before,
    'available_kib': available_kib,
    'R360_parent_slice': r360_parent_slice,
    'active_user_services': active_services,
    'active_docker_containers': docker_before,
    'docker_image_inspect': image,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'docker_caps': {'memory_reservation': '5g', 'memory': '7g', 'memory_swap': '7g (equal to memory; no swap)', 'pids_limit': 128, 'network': 'none', 'cgroup_parent': 'aspisr363.slice'},
    'planned_R360_parent_plus_R363_maximum': '14 GiB across parent and candidate scopes; all active reservations captured above and must fit host safety margin',
    'launch_revision': launch_revision,
    'source_revision': source_revision, 'parent_R360_launch_revision': parent_launch_revision,
    'candidate_source_tree_sha256_before_build': clone['R363_canonical_tree_sha256'],
    'candidate_NameMatcher_sha256': sha(src / 'NameMatcher.ml'),
    'R360_binary_sha256': sha(parent / 'aeneas-r360-comment-context-candidate'),
}
(audit / 'build-host-reservation-before.json').write_text(json.dumps(pre, indent=2) + '\n')
subprocess.run(['sudo', '-n', 'systemctl', 'set-property', '--runtime', 'aspisr363.slice', 'MemoryHigh=5G', 'MemoryMax=7G', 'MemorySwapMax=0', 'TasksMax=128'], check=True)
pre['R363_slice_before'] = subprocess.check_output(['systemctl', 'show', 'aspisr363.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'TasksMax', '-p', 'MemoryCurrent', '-p', 'MemoryPeak'], text=True)
(audit / 'build-host-reservation-before.json').write_text(json.dumps(pre, indent=2) + '\n')

inner = "set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r363-build/compiler-gnu-time.txt env AENEAS_VERSION=aspis-r363-instantiated-pattern-candidate-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r363-instantiated-pattern-candidate; chmod 755 /work/aeneas-r363-instantiated-pattern-candidate"
docker_cmd = ['docker', 'run', '--name', 'aspis-r363-instantiated-pattern-build', '--network', 'none', '--memory-reservation=5g', '--memory=7g', '--memory-swap=7g', '--pids-limit=128', '--cgroup-parent=aspisr363.slice', '-v', str(root) + ':/work', 'ef96e46342a4', 'bash', '-lc', inner]
command = {
    'docker_argv': docker_cmd,
    'inner_build_command': inner,
    'docker_image_id': image_id,
    'profile': 'dune build main.exe --profile release -j 1',
    'optimization': 'Dune release profile; static native link via OCAMLPARAM=_,ccopt=-static',
    'parallelism': {'OPAMJOBS': 1, 'DUNEJOBS': 1, 'dune_jobs': 1},
    'expected_work': 'cached compilation of changed NameMatcher.ml and llbc/LlbcAstUtils.ml plus necessary dependent compilation/native relink only; no cold dependency build, translation, or proof generation',
    'launch_revision': launch_revision,
    'source_revision': source_revision, 'parent_R360_launch_revision': parent_launch_revision,
    'R360_binary_sha256': '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416',
    'candidate_source_tree_sha256_before_build': clone['R363_canonical_tree_sha256'],
    'R360_ExtractTypes_sha256': '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    'R363_NameMatcher_sha256': 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8',
    'R363_LlbcAstUtils_sha256': '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97',
    'container_cgroup_peak_is_authoritative_for_container_memory': True,
    'docker_cli_time_rss_label': 'Docker CLI parent-process RSS only; not aggregate compiler or container RSS',
    'compiler_gnu_time_path': 'candidate-audit/r363-build/compiler-gnu-time.txt',
}
(audit / 'build-command.json').write_text(json.dumps(command, indent=2) + '\n')

cli_time = audit / 'docker-cli-time.txt'
log_path = audit / 'build.log'
with log_path.open('w') as log:
    process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(cli_time), *docker_cmd], stdout=log, stderr=subprocess.STDOUT, text=True)
    samples, paths = [], set()
    while process.poll() is None:
        try:
            inspect = json.loads(subprocess.check_output(['docker', 'inspect', 'aspis-r363-instantiated-pattern-build'], stderr=subprocess.DEVNULL, text=True))[0]
            pid = inspect.get('State', {}).get('Pid', 0)
            if pid:
                line = next((x for x in pathlib.Path(f'/proc/{pid}/cgroup').read_text().splitlines() if x.startswith('0::')), '')
                if line:
                    cgroup = pathlib.Path('/sys/fs/cgroup') / line.split('::', 1)[1].lstrip('/')
                    paths.add(str(cgroup)); sample = {'pid': pid, 'cgroup': str(cgroup)}
                    for filename in ('memory.current', 'memory.peak', 'memory.swap.current', 'memory.swap.peak', 'memory.events'):
                        try: sample[filename] = (cgroup / filename).read_text().strip()
                        except OSError: pass
                    samples.append(sample)
        except Exception as error:
            samples.append({'sample_error': type(error).__name__})
        time.sleep(.2)
status = process.returncode
try: docker_inspect = json.loads(subprocess.check_output(['docker', 'inspect', 'aspis-r363-instantiated-pattern-build'], text=True))
except subprocess.CalledProcessError: docker_inspect = []
(audit / 'docker-inspect.json').write_text(json.dumps(docker_inspect, indent=2) + '\n')
(audit / 'cgroup-samples.json').write_text(json.dumps({'samples': samples, 'observed_container_cgroup_paths': sorted(paths)}, indent=2) + '\n')
def numeric_max(key):
    vals=[]
    for sample in samples:
        try: vals.append(int(sample[key]))
        except (KeyError,ValueError): pass
    return max(vals) if vals else None
try: r363_after=subprocess.check_output(['systemctl','show','aspisr363.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)
except subprocess.CalledProcessError as error: r363_after='ERROR '+str(error)
r360_after=subprocess.check_output(['systemctl','show','aspisr360.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)
after={'meminfo_after':mem(),'R363_slice_after':r363_after,'R360_parent_slice_after':r360_after,'active_docker_containers_after':subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)}
(audit/'build-host-reservation-after.json').write_text(json.dumps(after,indent=2)+'\n')
binary=root/'aeneas-r363-instantiated-pattern-candidate'
result={'build_exit_status':status,'launch_revision':launch_revision,'source_revision':source_revision,'parent_R360_launch_revision':parent_launch_revision,'docker_image_id':image_id,'candidate_source_tree_sha256_before_build':clone['R363_canonical_tree_sha256'],'candidate_NameMatcher_sha256':sha(src/'NameMatcher.ml'),'candidate_LlbcAstUtils_sha256':sha(src/'llbc/LlbcAstUtils.ml'),'compiler_gnu_time_report_path':'candidate-audit/r363-build/compiler-gnu-time.txt','docker_cli_time_rss_boundary':'Docker CLI parent-process RSS only; not aggregate compiler or container RSS','container_cgroup_samples':len(samples),'observed_container_cgroup_paths':sorted(paths),'sampled_container_memory_peak_bytes':numeric_max('memory.peak'),'sampled_container_memory_swap_peak_bytes':numeric_max('memory.swap.peak'),'binary_exists':binary.is_file(),'binary_sha256':sha(binary) if binary.is_file() else None,'binary_size_bytes':binary.stat().st_size if binary.is_file() else None,'translation_or_Lean_compile_run':False}
(audit/'build-result.json').write_text(json.dumps(result,indent=2)+'\n')
print((log_path.read_text()[-12000:]) if status else f'R363_BUILD_EXIT {status}; build evidence saved under {audit}')
raise SystemExit(status)
