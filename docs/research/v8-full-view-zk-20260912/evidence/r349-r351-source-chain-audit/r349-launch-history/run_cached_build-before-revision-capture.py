# LAUNCH-CAPABLE RUNNER. Root launcher substitutes the actual source revision.
# Do not execute until the lead explicitly authorizes the build launch.
import hashlib, json, pathlib, subprocess, time

root = pathlib.Path('/home/dombarker/project-offloads/aspis-r349-output-name-alpha-candidate-20261002-a')
src = root / 'src'
audit = root / 'candidate-audit'
parent = pathlib.Path('/home/dombarker/project-offloads/aspis-r344-direct-empty-enum-candidate-20261002-a')
source_revision = 'R349_SOURCE_REVISION_PLACEHOLDER'
image_id = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

# Revalidate the saved source/cache clone audit and all direct source/binary hashes.
clone_audit = json.loads((audit / 'postpatch-clone-audit.json').read_text())
assert clone_audit['only_TranslateCore_changed'] is True
assert clone_audit['shared_regular_file_inodes'] == 0
assert clone_audit['R344_parent_unchanged_from_preclone_hash'] is True
assert clone_audit['candidate_postpatch_tree_sha256'] == '833502f292ecbdbfbba806fddd3d24a5fde5ac085d8088f0d29e86f61ed2f7e9'
assert src.is_dir() and (src / '_build/default/main.exe').is_file()
assert not (root / 'aeneas-r349-output-name-alpha-candidate').exists()
assert sha(src / 'TranslateCore.ml') == '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9'
assert sha(parent / 'src/TranslateCore.ml') == '2368456969bd85545b57cda2e701949b8814fc445a419b1e4e96795b91af57b7'
assert sha(src / 'interp/InterpExpansion.ml') == 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19'
assert sha(parent / 'src/interp/InterpExpansion.ml') == 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19'
assert sha(src / 'PrePasses.ml') == '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
assert sha(parent / 'src/PrePasses.ml') == '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
assert sha(parent / 'aeneas-r344-direct-empty-enum-candidate') == '7da5d7b8f3ade389eff0c87594609f5be24860b41eb171f55baa1b867896204b'

image = subprocess.check_output(['docker', 'image', 'inspect', 'ef96e46342a4', '--format', '{{.Id}} {{.Size}}'], text=True).strip()
assert image.startswith(image_id + ' '), image
existing = subprocess.check_output(['docker', 'ps', '-a', '--filter', 'name=aspis-r349-output-name-alpha-build', '--format', '{{.ID}} {{.Names}}'], text=True).strip()
assert not existing, existing
mem = lambda: {k: v for k, v in (line.split(':', 1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree')}
before = mem()
available_kib = int(before['MemAvailable'].split()[0])
assert available_kib >= 24 * 1024 * 1024, before
parent_slice = subprocess.check_output(['systemctl', 'show', 'aspisr344.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'MemoryCurrent'], text=True)
active_services = subprocess.check_output(['systemctl', '--user', 'list-units', '--type=service', '--state=running', '--no-legend'], text=True)
docker_before = subprocess.check_output(['docker', 'ps', '--no-trunc', '--format', '{{.ID}} {{.Names}} {{.Status}}'], text=True)
pre = {
    'meminfo_before': before,
    'available_kib': available_kib,
    'R344_parent_slice': parent_slice,
    'active_user_services': active_services,
    'active_docker_containers': docker_before,
    'docker_image_inspect': image,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'docker_caps': {'memory_reservation': '5g', 'memory': '7g', 'memory_swap': '7g (equal to memory; no swap)', 'pids_limit': 128, 'network': 'none', 'cgroup_parent': 'aspisr349.slice'},
    'planned_R344_plus_R349_maximum': '14 GiB across parent and candidate scopes; all other active build reservations are captured above and must fit the host policy',
    'source_revision': source_revision,
    'candidate_source_tree_sha256_before_build': clone_audit['candidate_postpatch_tree_sha256'],
    'candidate_TranslateCore_sha256': sha(src / 'TranslateCore.ml'),
    'parent_R344_binary_sha256': sha(parent / 'aeneas-r344-direct-empty-enum-candidate'),
}
(audit / 'build-host-reservation-before.json').write_text(json.dumps(pre, indent=2) + '\n')
subprocess.run(['sudo', '-n', 'systemctl', 'set-property', '--runtime', 'aspisr349.slice', 'MemoryHigh=5G', 'MemoryMax=7G', 'MemorySwapMax=0', 'TasksMax=128'], check=True)
pre['R349_slice_before'] = subprocess.check_output(['systemctl', 'show', 'aspisr349.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'TasksMax', '-p', 'MemoryCurrent', '-p', 'MemoryPeak'], text=True)
(audit / 'build-host-reservation-before.json').write_text(json.dumps(pre, indent=2) + '\n')

inner = "set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/compiler-gnu-time.txt env AENEAS_VERSION=aspis-r349-output-name-alpha-candidate-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r349-output-name-alpha-candidate; chmod 755 /work/aeneas-r349-output-name-alpha-candidate"
docker_cmd = ['docker', 'run', '--name', 'aspis-r349-output-name-alpha-build', '--network', 'none', '--memory-reservation=5g', '--memory=7g', '--memory-swap=7g', '--pids-limit=128', '--cgroup-parent=aspisr349.slice', '-v', str(root) + ':/work', 'ef96e46342a4', 'bash', '-lc', inner]
command = {
    'docker_argv': docker_cmd,
    'inner_build_command': inner,
    'docker_image_id': image_id,
    'profile': 'dune build main.exe --profile release -j 1',
    'optimization': 'Dune release profile; static native link via OCAMLPARAM=_,ccopt=-static',
    'parallelism': {'OPAMJOBS': 1, 'DUNEJOBS': 1, 'dune_jobs': 1},
    'expected_work': 'cached compilation of changed TranslateCore.ml plus native relink only; no cold dependency build, translation, or proof generation',
    'source_revision': source_revision,
    'parent_R344_binary_sha256': '7da5d7b8f3ade389eff0c87594609f5be24860b41eb171f55baa1b867896204b',
    'parent_source_tree_sha256': 'c84f1c1d6acdbe963999cadd0659a851a4608b1c08546f803e515d38b8f57c41',
    'candidate_source_tree_sha256_before_build': clone_audit['candidate_postpatch_tree_sha256'],
    'parent_TranslateCore_sha256': '2368456969bd85545b57cda2e701949b8814fc445a419b1e4e96795b91af57b7',
    'patched_TranslateCore_sha256': '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
    'unchanged_InterpExpansion_sha256': 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
    'unchanged_PrePasses_sha256': '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'container_cgroup_peak_is_authoritative_for_container_memory': True,
    'docker_cli_time_rss_label': 'Docker CLI parent-process RSS only; not aggregate compiler or container RSS',
    'compiler_gnu_time_path': 'candidate-audit/compiler-gnu-time.txt',
}
(audit / 'build-command.json').write_text(json.dumps(command, indent=2) + '\n')

# Docker CLI time is retained separately and must not be read as compiler RSS.
cli_time = audit / 'docker-cli-time.txt'
log_path = audit / 'build.log'
with log_path.open('w') as log:
    process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(cli_time), *docker_cmd], stdout=log, stderr=subprocess.STDOUT, text=True)
    samples = []
    paths = set()
    while process.poll() is None:
        try:
            inspect = json.loads(subprocess.check_output(['docker', 'inspect', 'aspis-r349-output-name-alpha-build'], stderr=subprocess.DEVNULL, text=True))[0]
            pid = inspect.get('State', {}).get('Pid', 0)
            if pid:
                cgroup_line = next((line for line in pathlib.Path(f'/proc/{pid}/cgroup').read_text().splitlines() if line.startswith('0::')), '')
                if cgroup_line:
                    cgroup = pathlib.Path('/sys/fs/cgroup') / cgroup_line.split('::', 1)[1].lstrip('/')
                    paths.add(str(cgroup))
                    sample = {'pid': pid, 'cgroup': str(cgroup)}
                    for filename in ('memory.current', 'memory.peak', 'memory.swap.current', 'memory.swap.peak', 'memory.events'):
                        try:
                            sample[filename] = (cgroup / filename).read_text().strip()
                        except OSError:
                            pass
                    samples.append(sample)
        except Exception as error:
            samples.append({'sample_error': type(error).__name__})
        time.sleep(.2)
status = process.returncode
try:
    docker_inspect = json.loads(subprocess.check_output(['docker', 'inspect', 'aspis-r349-output-name-alpha-build'], text=True))
except subprocess.CalledProcessError:
    docker_inspect = []
(audit / 'docker-inspect.json').write_text(json.dumps(docker_inspect, indent=2) + '\n')
(audit / 'cgroup-samples.json').write_text(json.dumps({'samples': samples, 'observed_container_cgroup_paths': sorted(paths)}, indent=2) + '\n')

def numeric_sample_max(key):
    vals = []
    for sample in samples:
        try:
            vals.append(int(sample[key]))
        except (KeyError, ValueError):
            pass
    return max(vals) if vals else None

try:
    r349_after = subprocess.check_output(['systemctl', 'show', 'aspisr349.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'TasksMax', '-p', 'MemoryCurrent', '-p', 'MemoryPeak', '-p', 'MemorySwapCurrent', '-p', 'MemorySwapPeak'], text=True)
except subprocess.CalledProcessError as error:
    r349_after = 'ERROR ' + str(error)
r344_after = subprocess.check_output(['systemctl', 'show', 'aspisr344.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'MemoryCurrent', '-p', 'MemoryPeak', '-p', 'MemorySwapCurrent', '-p', 'MemorySwapPeak'], text=True)
after = {'meminfo_after': mem(), 'R349_slice_after': r349_after, 'R344_parent_slice_after': r344_after, 'active_docker_containers_after': subprocess.check_output(['docker', 'ps', '--no-trunc', '--format', '{{.ID}} {{.Names}} {{.Status}}'], text=True)}
(audit / 'build-host-reservation-after.json').write_text(json.dumps(after, indent=2) + '\n')

binary = root / 'aeneas-r349-output-name-alpha-candidate'
result = {
    'build_exit_status': status,
    'source_revision': source_revision,
    'docker_image_id': image_id,
    'parent_R344_binary_sha256': sha(parent / 'aeneas-r344-direct-empty-enum-candidate'),
    'parent_source_unchanged': sha(parent / 'src/TranslateCore.ml') == '2368456969bd85545b57cda2e701949b8814fc445a419b1e4e96795b91af57b7' and sha(parent / 'src/interp/InterpExpansion.ml') == 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19' and sha(parent / 'src/PrePasses.ml') == '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'candidate_TranslateCore_sha256': sha(src / 'TranslateCore.ml'),
    'candidate_InterpExpansion_sha256': sha(src / 'interp/InterpExpansion.ml'),
    'candidate_PrePasses_sha256': sha(src / 'PrePasses.ml'),
    'docker_cli_time_report_path': 'candidate-audit/docker-cli-time.txt',
    'docker_cli_time_rss_boundary': 'Docker CLI parent-process RSS only; not aggregate compiler or container RSS',
    'compiler_gnu_time_path': 'candidate-audit/compiler-gnu-time.txt',
    'container_cgroup_samples': len(samples),
    'observed_container_cgroup_paths': sorted(paths),
    'sampled_container_memory_peak_bytes': numeric_sample_max('memory.peak'),
    'sampled_container_memory_swap_peak_bytes': numeric_sample_max('memory.swap.peak'),
    'binary_exists': binary.is_file(),
    'binary_sha256': sha(binary) if binary.is_file() else None,
    'binary_size_bytes': binary.stat().st_size if binary.is_file() else None,
    'translation_or_Lean_compile_run': False,
}
(audit / 'build-result.json').write_text(json.dumps(result, indent=2) + '\n')
print((log_path.read_text()[-12000:]) if status else f'R349_BUILD_EXIT {status}; build evidence saved under {audit}')
raise SystemExit(status)
