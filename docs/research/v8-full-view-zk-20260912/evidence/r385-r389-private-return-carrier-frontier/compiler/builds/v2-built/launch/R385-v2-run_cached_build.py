#!/usr/bin/env python3
"""R385 v2 capped cached compiler runner. One changed-source attempt; translation and Lean are not run here."""
import hashlib, json, pathlib, subprocess, time

root = pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
src = root / 'src'
audit = root / 'candidate-audit/r385-v2-build'
parent = pathlib.Path('/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a')
launch_revision = 'a962b9ac222caa6d2f715882240b9b9856158261'
image_id = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
CANDIDATE_PRE = '579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17'
PARENT_PRE = '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
NAME = 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8'
LLBC_UTILS = '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97'
CACHED_BIN = '3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

assert len(launch_revision) == 40 and all(c in '0123456789abcdef' for c in launch_revision), launch_revision
assert src.is_dir() and audit.is_dir()
assert sha(src / 'PrePasses.ml') == CANDIDATE_PRE
assert sha(parent / 'src/PrePasses.ml') == PARENT_PRE
assert sha(src / 'NameMatcher.ml') == NAME
assert sha(src / 'llbc/LlbcAstUtils.ml') == LLBC_UTILS
assert sha(src / '_build/default/main.exe') == CACHED_BIN
assert sha(parent / 'src/_build/default/main.exe') == CACHED_BIN
assert not (root / 'aeneas-r385-private-return-carrier-v2-candidate').exists()
assert sorted(p.name for p in audit.iterdir()) == ['run_cached_build.py']
assert not (audit / 'build-result.json').exists()

image = subprocess.check_output(['docker', 'image', 'inspect', 'ef96e46342a4', '--format', '{{.Id}} {{.Size}}'], text=True).strip()
assert image.startswith(image_id + ' '), image
existing = subprocess.check_output(['docker', 'ps', '-a', '--filter', 'name=aspis-r385-private-return-carrier-v2-build', '--format', '{{.ID}} {{.Names}}'], text=True).strip()
assert not existing, existing
mem = lambda: {k: v for k, v in (line.split(':', 1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree')}
before = mem()
available_kib = int(before['MemAvailable'].split()[0])
assert available_kib >= 24 * 1024 * 1024, before
active_services = subprocess.check_output(['systemctl', '--user', 'list-units', '--type=service', '--state=running', '--no-legend'], text=True)
docker_before = subprocess.check_output(['docker', 'ps', '--no-trunc', '--format', '{{.ID}} {{.Names}} {{.Status}}'], text=True)
pre = {
    'meminfo_before': before, 'available_kib': available_kib,
    'active_user_services': active_services, 'active_docker_containers': docker_before,
    'docker_image_inspect': image,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'docker_caps': {'memory_reservation': '5g', 'memory': '7g', 'memory_swap': '7g (equal to memory; no swap)', 'pids_limit': 128, 'network': 'none', 'cgroup_parent': 'aspisr385.slice'},
    'launch_revision': launch_revision,
    'candidate_PrePasses_sha256': sha(src / 'PrePasses.ml'),
    'parent_PrePasses_sha256': sha(parent / 'src/PrePasses.ml'),
    'inherited_NameMatcher_sha256': sha(src / 'NameMatcher.ml'),
    'inherited_LlbcAstUtils_sha256': sha(src / 'llbc/LlbcAstUtils.ml'),
    'cached_R363_binary_sha256': sha(src / '_build/default/main.exe'),
    'expected_work': 'Cached PrePasses.ml compilation and only necessary dependent compilation/native relink; translation and Lean are outside this runner.',
    'cache_provenance': 'This _build cache was used by failed R385 v1. The main.exe remains the original R363 binary by SHA, but other _build entries are not claimed byte-identical to pristine R363.'
}
(audit / 'build-host-reservation-before.json').write_text(json.dumps(pre, indent=2) + '\n')
subprocess.run(['sudo', '-n', 'systemctl', 'set-property', '--runtime', 'aspisr385.slice', 'MemoryHigh=5G', 'MemoryMax=7G', 'MemorySwapMax=0', 'TasksMax=128'], check=True)
pre['R385_slice_before'] = subprocess.check_output(['systemctl', 'show', 'aspisr385.slice', '-p', 'MemoryHigh', '-p', 'MemoryMax', '-p', 'MemorySwapMax', '-p', 'TasksMax', '-p', 'MemoryCurrent', '-p', 'MemoryPeak'], text=True)
(audit / 'build-host-reservation-before.json').write_text(json.dumps(pre, indent=2) + '\n')

inner = "set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r385-v2-build/compiler-gnu-time.txt env AENEAS_VERSION=aspis-r385-private-return-carrier-v2-candidate-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r385-private-return-carrier-v2-candidate; chmod 755 /work/aeneas-r385-private-return-carrier-v2-candidate"
docker_cmd = ['docker', 'run', '--name', 'aspis-r385-private-return-carrier-v2-build', '--network', 'none', '--memory-reservation=5g', '--memory=7g', '--memory-swap=7g', '--pids-limit=128', '--cgroup-parent=aspisr385.slice', '-v', str(root) + ':/work', 'ef96e46342a4', 'bash', '-lc', inner]
command = {
    'docker_argv': docker_cmd, 'inner_build_command': inner,
    'docker_image_id': image_id, 'profile': 'dune build main.exe --profile release -j 1',
    'optimization': 'Dune release profile; static native link via OCAMLPARAM=_,ccopt=-static',
    'parallelism': {'OPAMJOBS': 1, 'DUNEJOBS': 1, 'dune_jobs': 1},
    'launch_revision': launch_revision,
    'source_hashes': {'candidate_PrePasses': CANDIDATE_PRE, 'parent_PrePasses': PARENT_PRE, 'NameMatcher': NAME, 'LlbcAstUtils': LLBC_UTILS, 'cached_R363_binary': CACHED_BIN},
    'prior_R385_v1_attempt': {'exit_status': 1, 'wall_seconds': 3.25, 'container_cgroup_peak_bytes': 555118592, 'swap_peak_bytes': 0, 'source_sha256': 'ea353ee571da9d5c00f5fa6bc7041954eb3c10b3ac5abe9798d1b3bdbcafcb75'},
    'container_cgroup_peak_is_authoritative_for_container_memory': True,
    'docker_cli_time_rss_label': 'Docker CLI parent-process RSS only; not aggregate compiler or container RSS',
    'compiler_gnu_time_path': 'candidate-audit/r385-v2-build/compiler-gnu-time.txt'
}
(audit / 'build-command.json').write_text(json.dumps(command, indent=2) + '\n')

cli_time = audit / 'docker-cli-time.txt'
log_path = audit / 'build.log'
with log_path.open('w') as log:
    process = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(cli_time), *docker_cmd], stdout=log, stderr=subprocess.STDOUT, text=True)
    samples, paths = [], set()
    while process.poll() is None:
        try:
            inspect = json.loads(subprocess.check_output(['docker', 'inspect', 'aspis-r385-private-return-carrier-v2-build'], stderr=subprocess.DEVNULL, text=True))[0]
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
try: docker_inspect = json.loads(subprocess.check_output(['docker', 'inspect', 'aspis-r385-private-return-carrier-v2-build'], text=True))
except subprocess.CalledProcessError: docker_inspect = []
(audit / 'docker-inspect.json').write_text(json.dumps(docker_inspect, indent=2) + '\n')
(audit / 'cgroup-samples.json').write_text(json.dumps({'samples': samples, 'observed_container_cgroup_paths': sorted(paths)}, indent=2) + '\n')
def numeric_max(key):
    vals=[]
    for sample in samples:
        try: vals.append(int(sample[key]))
        except (KeyError, ValueError): pass
    return max(vals) if vals else None
try: slice_after = subprocess.check_output(['systemctl','show','aspisr385.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)
except subprocess.CalledProcessError as error: slice_after='ERROR '+str(error)
after = {'meminfo_after': mem(), 'R385_slice_after': slice_after, 'active_docker_containers_after': subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)}
(audit / 'build-host-reservation-after.json').write_text(json.dumps(after, indent=2) + '\n')
binary = root / 'aeneas-r385-private-return-carrier-v2-candidate'
result = {
    'build_exit_status': status, 'launch_revision': launch_revision, 'docker_image_id': image_id,
    'candidate_PrePasses_sha256': sha(src / 'PrePasses.ml'),
    'compiler_gnu_time_report_path': 'candidate-audit/r385-v2-build/compiler-gnu-time.txt',
    'docker_cli_time_rss_boundary': 'Docker CLI parent-process RSS only; not aggregate compiler or container RSS',
    'container_cgroup_samples': len(samples), 'observed_container_cgroup_paths': sorted(paths),
    'sampled_container_memory_peak_bytes': numeric_max('memory.peak'),
    'sampled_container_memory_swap_peak_bytes': numeric_max('memory.swap.peak'),
    'binary_exists': binary.is_file(), 'binary_sha256': sha(binary) if binary.is_file() else None,
    'binary_size_bytes': binary.stat().st_size if binary.is_file() else None,
    'translation_or_Lean_compile_run': False
}
(audit / 'build-result.json').write_text(json.dumps(result, indent=2) + '\n')
print((log_path.read_text()[-12000:]) if status else f'R385_V2_BUILD_EXIT {status}; build evidence saved under {audit}')
raise SystemExit(status)
