#!/usr/bin/env python3
"""Root launcher. Prepared for review only; do not invoke without lead authorization."""
import datetime, hashlib, json, pathlib, shlex, shutil, subprocess

here = pathlib.Path(__file__).resolve().parent
runner = here / 'run_cached_build.py'
host = 'dombarker@100.108.41.90'
remote_root = '/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a'
remote_audit = remote_root + '/candidate-audit'
remote_runner = remote_audit + '/run_cached_build.py'
ssh_options = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']

# Runs only after explicit lead launch authorization.
launch_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
assert len(launch_revision) == 40 and all(c in '0123456789abcdef' for c in launch_revision), launch_revision
pristine_runner = runner.read_text()
assert pristine_runner.count('R360_LAUNCH_REVISION_PLACEHOLDER') == 1
for expected in (
    '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    'cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25',
    'dc4b9d209c645a0d951bdd78f7e0f9d6fb9d09b0e88491edded1ee7beb791cd6',
    'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
    '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7',
):
    assert expected in pristine_runner, expected

stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history = here / 'history' / ('launch-' + launch_revision[:12] + '-' + stamp)
history.mkdir(parents=True, exist_ok=False)
shutil.copy2(runner, history / 'run_cached_build-before-revision-capture.py')
shutil.copy2(__file__, history / 'launch_build.py')
materialized_runner = pristine_runner.replace('R360_LAUNCH_REVISION_PLACEHOLDER', launch_revision)
runner.write_text(materialized_runner)
runner_sha = hashlib.sha256(runner.read_bytes()).hexdigest()

# Create candidate-audit only if absent. Existing contents are never replaced here.
ensure_audit_code = (
    "from pathlib import Path\n"
    + "p=Path(" + repr(remote_audit) + ")\n"
    + "if p.exists():\n"
    + "    assert p.is_dir() and not p.is_symlink()\n"
    + "else:\n"
    + "    p.mkdir(parents=True, exist_ok=False)\n"
)
ensure_audit = "python3 -c " + shlex.quote(ensure_audit_code)
subprocess.run(['ssh', *ssh_options, host, ensure_audit], check=True)
remote_preflight = (
    f'test -d {shlex.quote(remote_root + "/src")} && '
    f'test -d {shlex.quote(remote_audit)} && '
    f'test ! -e {shlex.quote(remote_runner)} && '
    f'test ! -e {shlex.quote(remote_root + "/aeneas-r360-comment-context-candidate")} && '
    f'test ! -e {shlex.quote(remote_audit + "/build-command.json")} && '
    f'test ! -e {shlex.quote(remote_audit + "/build-result.json")} && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/TranslateCore.ml")} | cut -d" " -f1)" = '
    f'4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/extract/ExtractTypes.ml")} | cut -d" " -f1)" = '
    f'0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/src/_build/default/main.exe")} | cut -d" " -f1)" = '
    f'dc4b9d209c645a0d951bdd78f7e0f9d6fb9d09b0e88491edded1ee7beb791cd6 && '
    f'test "$(sha256sum {shlex.quote(remote_root + "/candidate-audit/candidate-tree-manifest.json")} | cut -d" " -f1)" = '
    f'27820ee9cc6706001009c240280c24d156c0dff9e52e8b130dccb815ca7d05e2'
)
subprocess.run(['ssh', *ssh_options, host, remote_preflight], check=True)
subprocess.run(['scp', *ssh_options, str(runner), host + ':' + remote_runner], check=True)

argv = [
    'systemd-run', '--user', '--wait', '--collect', '--pipe',
    '--unit=aspis-r360-comment-names-build',
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
    'candidate_audit_directory_existence': 'ensure only if absent; existing audit files are never replaced by this step',
    'systemd_run_argv': argv,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'docker_caps': {'memory_reservation': '5g', 'memory': '7g', 'memory_swap': '7g (equal to memory; zero swap)', 'network': 'none', 'pids_limit': 128, 'cgroup_parent': 'aspisr360.slice'},
    'parent_R349_binary_sha256': 'dc4b9d209c645a0d951bdd78f7e0f9d6fb9d09b0e88491edded1ee7beb791cd6',
    'candidate_ExtractTypes_sha256': '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    'expected_step': 'Cached ExtractTypes.ml compilation plus native relink and necessary dependent compilation only.',
    'resource_and_measurement_note': 'Offline pinned image; compiler GNU time and actual container cgroup sampling are separate; Docker CLI RSS is only its parent process RSS.',
    'launch_authorization': 'Root launcher prepared only; invocation requires lead review and explicit authorization.',
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
