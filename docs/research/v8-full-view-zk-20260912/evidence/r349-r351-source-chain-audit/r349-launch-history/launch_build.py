#!/usr/bin/env python3
"""Root launcher. Prepared for review only; do not invoke before build authorization."""
import datetime, hashlib, json, pathlib, shlex, shutil, subprocess

here = pathlib.Path(__file__).resolve().parent
runner = here / 'run_cached_build.py'
host = 'dombarker@100.108.41.90'
remote_root = '/home/dombarker/project-offloads/aspis-r349-output-name-alpha-candidate-20261002-a'
remote_audit = remote_root + '/candidate-audit'
remote_runner = remote_audit + '/run_cached_build.py'
ssh_options = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']

# This executes only when the lead explicitly runs the launcher after review.
source_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
assert len(source_revision) == 40 and all(c in '0123456789abcdef' for c in source_revision), source_revision
pristine_runner = runner.read_text()
assert pristine_runner.count('R349_SOURCE_REVISION_PLACEHOLDER') == 1
assert '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9' in pristine_runner
assert 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19' in pristine_runner
assert '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd' in pristine_runner

stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history = here / 'history' / ('launch-' + source_revision[:12] + '-' + stamp)
history.mkdir(parents=True, exist_ok=False)
shutil.copy2(runner, history / 'run_cached_build-before-revision-capture.py')
shutil.copy2(__file__, history / 'launch_build.py')
materialized_runner = pristine_runner.replace('R349_SOURCE_REVISION_PLACEHOLDER', source_revision)
runner.write_text(materialized_runner)
runner_sha = hashlib.sha256(runner.read_bytes()).hexdigest()

# Refuse to replace any pre-existing remote runner or output binary.
remote_preflight = (
    f'test -d {shlex.quote(remote_root + "/src")} && '
    f'test -d {shlex.quote(remote_audit)} && '
    f'test ! -e {shlex.quote(remote_runner)} && '
    f'test ! -e {shlex.quote(remote_root + "/aeneas-r349-output-name-alpha-candidate")} && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/TranslateCore.ml")} | cut -d" " -f1)" = '
    f'4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/interp/InterpExpansion.ml")} | cut -d" " -f1)" = '
    f'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/PrePasses.ml")} | cut -d" " -f1)" = '
    f'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
)
subprocess.run(['ssh', *ssh_options, host, remote_preflight], check=True)
subprocess.run(['scp', *ssh_options, str(runner), host + ':' + remote_runner], check=True)

argv = [
    'systemd-run', '--user', '--wait', '--collect', '--pipe',
    '--unit=aspis-r349-output-name-alpha-build',
    '--working-directory=' + remote_root + '/src',
    '-p', 'MemoryHigh=5G', '-p', 'MemoryMax=7G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=128',
    'python3', remote_runner,
]
receipt = {
    'source_revision_captured_at_launch': source_revision,
    'launch_preparation_timestamp_utc': stamp,
    'runner_sha256_after_revision_capture': runner_sha,
    'remote_runner': remote_runner,
    'systemd_run_argv': argv,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'parent_R344_binary_sha256': '7da5d7b8f3ade389eff0c87594609f5be24860b41eb171f55baa1b867896204b',
    'candidate_TranslateCore_sha256': '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
    'unchanged_InterpExpansion_sha256': 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
    'unchanged_PrePasses_sha256': '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'expected_step': 'Cached TranslateCore.ml compilation plus native relink only.',
    'resource_and_measurement_note': 'Runner uses offline pinned image; systemd and Docker caps are 5/7 GiB with zero swap and 128 tasks/pids. Compiler GNU time and container cgroup sampling are saved separately; Docker CLI RSS is explicitly labeled as the CLI parent process only.',
    'build_authorization': 'This launcher must only be invoked after lead review and explicit launch authorization.',
}
(history / 'launch-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
log = here / ('build-launch-' + source_revision[:12] + '-' + stamp + '.log')
log.parent.mkdir(exist_ok=True)
with log.open('w') as out:
    proc = subprocess.run(['ssh', *ssh_options, host, shlex.join(argv)], stdout=out, stderr=subprocess.STDOUT)
receipt['launcher_exit_status'] = proc.returncode
(history / 'launch-result.json').write_text(json.dumps(receipt, indent=2) + '\n')
# Preserve the full host-side evidence separately from source/inode audit artifacts.
evidence = here / 'build-evidence' / (source_revision[:12] + '-' + stamp)
evidence.mkdir(parents=True, exist_ok=False)
subprocess.run(['scp', '-r', *ssh_options, host + ':' + remote_audit + '/.', str(evidence)], check=True)
print(json.dumps({'exit_status': proc.returncode, 'source_revision': source_revision, 'runner_sha256': runner_sha, 'launch_log': str(log), 'evidence_dir': str(evidence)}, indent=2))
raise SystemExit(proc.returncode)
