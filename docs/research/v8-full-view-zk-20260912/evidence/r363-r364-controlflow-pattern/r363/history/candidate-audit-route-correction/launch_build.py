#!/usr/bin/env python3
"""R363 root launcher; prepared only, do not invoke before lead authorization."""
import datetime, hashlib, json, pathlib, shlex, shutil, subprocess

here = pathlib.Path(__file__).resolve().parent
runner = here / 'run_cached_build.py'
host = 'dombarker@100.108.41.90'
remote_root = '/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a'
parent_root = '/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a'
remote_audit = remote_root + '/candidate-audit'
remote_runner = remote_audit + '/run_cached_build.py'
ssh_options = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']

def remote(command):
    return subprocess.run(['ssh', *ssh_options, host, command], check=True)

launch_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
assert len(launch_revision) == 40 and all(c in '0123456789abcdef' for c in launch_revision), launch_revision
pristine_runner = runner.read_text()
assert pristine_runner.count('R363_LAUNCH_REVISION_PLACEHOLDER') == 1
for expected in (
    'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8',
    '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97',
    '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416',
    'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
    '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7',
    'e43845424aeb6964281bd0d5e9d7ba4beb3d0a0aefe10b8acdab382127503e89',
    '7b0482d1ea4b068ece18267002cdcd7dd24689f18b6909e2964cbe6bb5bba275',
):
    assert expected in pristine_runner, expected

stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history = here / 'history' / ('launch-' + launch_revision[:12] + '-' + stamp)
history.mkdir(parents=True, exist_ok=False)
shutil.copy2(runner, history / 'run_cached_build-before-revision-capture.py')
shutil.copy2(__file__, history / 'launch_build.py')
runner.write_text(pristine_runner.replace('R363_LAUNCH_REVISION_PLACEHOLDER', launch_revision))
runner_sha = hashlib.sha256(runner.read_bytes()).hexdigest()

# Fail closed unless the reviewed source/cache manifests and all changed-file hashes match.
remote_preflight = (
    f'test -d {shlex.quote(remote_root + "/src")} && '
    f'test -d {shlex.quote(remote_audit)} && '
    f'test "$(sha256sum {shlex.quote(parent_root + "/aeneas-r360-comment-context-candidate")} | cut -d" " -f1)" = '
    f'8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416 && '
    f'test ! -e {shlex.quote(remote_runner)} && '
    f'test ! -e {shlex.quote(remote_root + "/aeneas-r363-instantiated-pattern-candidate")} && '
    f'test ! -e {shlex.quote(remote_audit + "/build-command.json")} && '
    f'test ! -e {shlex.quote(remote_audit + "/build-result.json")} && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/NameMatcher.ml")} | cut -d" " -f1)" = '
    f'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/llbc/LlbcAstUtils.ml")} | cut -d" " -f1)" = '
    f'17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/extract/ExtractTypes.ml")} | cut -d" " -f1)" = '
    f'0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/_build/default/main.exe")} | cut -d" " -f1)" = '
    f'8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416 && '
    f'test "$(sha256sum {shlex.quote(remote_audit + "/R363-source-tree-manifest.json")} | cut -d" " -f1)" = '
    f'e43845424aeb6964281bd0d5e9d7ba4beb3d0a0aefe10b8acdab382127503e89 && '
    f'test "$(sha256sum {shlex.quote(remote_audit + "/clone-audit.json")} | cut -d" " -f1)" = '
    f'7b0482d1ea4b068ece18267002cdcd7dd24689f18b6909e2964cbe6bb5bba275'
)
remote(remote_preflight)
subprocess.run(['scp', *ssh_options, str(runner), host + ':' + remote_runner], check=True)

argv = [
    'systemd-run', '--user', '--wait', '--collect', '--pipe',
    '--unit=aspis-r363-instantiated-pattern-build',
    '--working-directory=' + remote_root + '/src',
    '-p', 'MemoryHigh=5G', '-p', 'MemoryMax=7G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=128',
    'python3', remote_runner,
]
receipt = {
    'launch_revision_captured_at_launch': launch_revision,
    'launch_preparation_timestamp_utc': stamp,
    'runner_sha256_after_revision_capture': runner_sha,
    'remote_runner': remote_runner,
    'candidate_remote_root': remote_root,
    'parent_remote_root': parent_root,
    'parent_R360_launch_revision': '078a3bd7d4471a5f10549843e7818b956163bb77',
    'campaign_source_revision': '56a931fc3879354a2fa584e73bd0a1d412714851',
    'systemd_run_argv': argv,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'docker_caps': {'memory_reservation': '5g', 'memory': '7g', 'memory_swap': '7g (equal to memory; zero swap)', 'network': 'none', 'pids_limit': 128, 'cgroup_parent': 'aspisr363.slice'},
    'parent_R360_binary_sha256': '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416',
    'candidate_NameMatcher_sha256': 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8',
    'candidate_LlbcAstUtils_sha256': '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97',
    'candidate_manifest_sha256': 'e43845424aeb6964281bd0d5e9d7ba4beb3d0a0aefe10b8acdab382127503e89',
    'candidate_clone_audit_sha256': '7b0482d1ea4b068ece18267002cdcd7dd24689f18b6909e2964cbe6bb5bba275',
    'expected_step': 'Cached NameMatcher.ml and LlbcAstUtils.ml compilation plus necessary dependent compilation/native relink only.',
    'resource_and_measurement_note': 'Offline pinned image; GNU time and actual container cgroup sampling are separate; Docker CLI RSS is only its parent process RSS.',
    'launch_authorization': 'Preparation only; this launcher must be reviewed and explicitly launched by the lead.',
}
(history / 'launch-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
log = here / ('build-launch-' + launch_revision[:12] + '-' + stamp + '.log')
with log.open('w') as out:
    proc = subprocess.run(['ssh', *ssh_options, host, shlex.join(argv)], stdout=out, stderr=subprocess.STDOUT)
receipt['launcher_exit_status'] = proc.returncode
(history / 'launch-result.json').write_text(json.dumps(receipt, indent=2) + '\n')
evidence = here / 'build-evidence' / (launch_revision[:12] + '-' + stamp)
evidence.mkdir(parents=True, exist_ok=False)
subprocess.run(['scp', '-r', *ssh_options, host + ':' + remote_audit + '/.', str(evidence)], check=True)
print(json.dumps({'exit_status': proc.returncode, 'launch_revision': launch_revision, 'runner_sha256': runner_sha, 'launch_log': str(log), 'evidence_dir': str(evidence)}, indent=2))
raise SystemExit(proc.returncode)
