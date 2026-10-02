#!/usr/bin/env python3
"""R385 v2 changed-source launcher. Default invocation is local preflight-only."""
import argparse, datetime, hashlib, json, pathlib, shlex, subprocess

HERE = pathlib.Path(__file__).resolve().parent
TASK = HERE.parent
WORKTREE = TASK.parents[1]
ROOT = pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
PARENT = pathlib.Path('/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a')
AUDIT = ROOT / 'candidate-audit/r385-v2-build'
SOURCE_HISTORY = ROOT / 'candidate-audit/r385-v2-source-history'
HOST = 'dombarker@100.108.41.90'
RUNNER_TEMPLATE = HERE / 'R385-v2-run_cached_build.py'
V1 = 'ea353ee571da9d5c00f5fa6bc7041954eb3c10b3ac5abe9798d1b3bdbcafcb75'
V2 = '579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17'
PARENT_PRE = '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
NAME = 'bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8'
LLBC_UTILS = '17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97'
CACHED_BIN = '3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329'
ssh_options = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def local_preflight():
    v1_path = TASK / 'history/PrePasses.candidate-v1-typeid-error.ml'
    v2_path = TASK / 'PrePasses.candidate.ml'
    repair = json.loads((TASK / 'history/candidate-v2-repair.json').read_text())
    prior = json.loads((TASK / 'build-evidence/a962b9ac222c-20261002T152844Z/build-result.json').read_text())
    option = json.loads((HERE / 'R327-option-preflight.json').read_text())
    v1_bytes = v1_path.read_bytes(); v2_bytes = v2_path.read_bytes()
    assert hashlib.sha256(v1_bytes).hexdigest() == V1
    assert hashlib.sha256(v2_bytes).hexdigest() == V2 == repair['candidate_sha256']
    assert v2_bytes == v1_bytes.replace(b'(TypeId id, name)', b'(IdType id, name)')
    assert v1_bytes.count(b'(TypeId id, name)') == 2
    assert prior['build_exit_status'] == 1 and prior['binary_exists'] is False
    assert option['input_llbc']['sha256'] == '9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
    assert option['option_count'] == 3 and option['def_ids'] == [9, 12, 13]
    assert RUNNER_TEMPLATE.read_text().count('R385_V2_LAUNCH_REVISION_PLACEHOLDER') == 1
    return {'v1_sha256': V1, 'v2_sha256': V2, 'v2_delta': 'exactly two TypeId -> IdType constructor replacements', 'prior_v1_exit_status': 1, 'cached_R363_main_exe_sha256': CACHED_BIN, 'R327_LLBC_sha256': option['input_llbc']['sha256'], 'R327_option_count': 3}

def remote(command):
    return subprocess.run(['ssh', *ssh_options, HOST, command], check=True, text=True, capture_output=True).stdout

parser = argparse.ArgumentParser()
parser.add_argument('--lead-reviewed-r385-v2-build', action='store_true', help='apply the reviewed two-constructor source correction and run exactly one capped cached build')
args = parser.parse_args()
local = local_preflight()
if not args.lead_reviewed_r385_v2_build:
    print(json.dumps({'status': 'PREPARED_ONLY; no SSH, source update, cgroup reservation, build, translation, or Lean run performed', 'local_preflight': local, 'required_to_launch': '--lead-reviewed-r385-v2-build'}, indent=2))
    raise SystemExit(0)

launch_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=WORKTREE, text=True).strip()
assert len(launch_revision) == 40 and all(c in '0123456789abcdef' for c in launch_revision), launch_revision
timestamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
history = TASK / 'history' / ('launch-v2-' + launch_revision[:12] + '-' + timestamp)
history.mkdir(parents=True, exist_ok=False)
template = RUNNER_TEMPLATE.read_text()
runner_tmp = history / 'R385-v2-run_cached_build.py'
runner_tmp.write_text(template.replace('R385_V2_LAUNCH_REVISION_PLACEHOLDER', launch_revision))
runner_sha = sha(runner_tmp)
remote_runner = str(AUDIT / 'run_cached_build.py')
remote_v1_backup = str(SOURCE_HISTORY / 'PrePasses.v1.ml')

preflight = 'set -eu; ' + ' && '.join([
    f'test -d {shlex.quote(str(ROOT / "src"))}',
    f'test ! -e {shlex.quote(str(AUDIT))}',
    f'test ! -e {shlex.quote(str(SOURCE_HISTORY))}',
    f'test ! -e {shlex.quote(str(ROOT / "aeneas-r385-private-return-carrier-v2-candidate"))}',
    f'test "$(sha256sum {shlex.quote(str(ROOT / "src/PrePasses.ml"))} | cut -d" " -f1)" = {V1}',
    f'test "$(sha256sum {shlex.quote(str(PARENT / "src/PrePasses.ml"))} | cut -d" " -f1)" = {PARENT_PRE}',
    f'test "$(sha256sum {shlex.quote(str(ROOT / "src/NameMatcher.ml"))} | cut -d" " -f1)" = {NAME}',
    f'test "$(sha256sum {shlex.quote(str(ROOT / "src/llbc/LlbcAstUtils.ml"))} | cut -d" " -f1)" = {LLBC_UTILS}',
    f'test "$(sha256sum {shlex.quote(str(ROOT / "src/_build/default/main.exe"))} | cut -d" " -f1)" = {CACHED_BIN}',
    f'test "$(sha256sum {shlex.quote(str(PARENT / "src/_build/default/main.exe"))} | cut -d" " -f1)" = {CACHED_BIN}',
    f'test ! -e {shlex.quote(remote_v1_backup)}'
])
remote(preflight)

# Preserve the exact remote v1 file outside the new build-result directory, then install the reviewed v2 source.
remote('mkdir ' + shlex.quote(str(SOURCE_HISTORY)) + ' && cp ' + shlex.quote(str(ROOT / 'src/PrePasses.ml')) + ' ' + shlex.quote(remote_v1_backup))
subprocess.run(['scp', *ssh_options, str(TASK / 'PrePasses.candidate.ml'), HOST + ':' + str(ROOT / 'src/PrePasses.ml')], check=True)
postpatch = remote('set -eu; test "$(sha256sum ' + shlex.quote(str(ROOT / 'src/PrePasses.ml')) + ' | cut -d" " -f1)" = ' + V2 + '; sha256sum ' + shlex.quote(remote_v1_backup) + ' ' + shlex.quote(str(ROOT / 'src/PrePasses.ml')))
subprocess.run(['ssh', *ssh_options, HOST, 'mkdir ' + shlex.quote(str(AUDIT))], check=True)
subprocess.run(['scp', *ssh_options, str(runner_tmp), HOST + ':' + remote_runner], check=True)

argv = [
    'systemd-run', '--user', '--wait', '--collect', '--pipe',
    '--unit=aspis-r385-private-return-carrier-v2-build',
    '--working-directory=' + str(ROOT / 'src'),
    '-p', 'MemoryHigh=5G', '-p', 'MemoryMax=7G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=128',
    'python3', remote_runner,
]
receipt = {
    'status': 'authorized one changed-source v2 attempt',
    'launch_revision_captured_at_launch': launch_revision,
    'timestamp_utc': timestamp,
    'candidate_root': str(ROOT), 'parent_root': str(PARENT),
    'v1_remote_backup': remote_v1_backup, 'v1_backup_and_v2_patch_result': postpatch,
    'runner_sha256_after_revision_capture': runner_sha, 'remote_runner': remote_runner,
    'local_preflight': local, 'remote_prepatch_checks': preflight,
    'systemd_run_argv': argv,
    'systemd_caps': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128},
    'container_caps': {'memory_reservation': '5g', 'memory': '7g', 'memory_swap': '7g (equal to memory; zero swap)', 'pids_limit': 128, 'network': 'none', 'cgroup_parent': 'aspisr385.slice'},
    'pinned_image_id': 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7',
    'cache_boundary': 'The preserved R363 _build cache was touched by the failed v1 attempt. Its cached main.exe SHA is still the R363 SHA, but other cache entries are not claimed identical to pristine R363.',
    'translation_or_Lean_compile': False,
}
(history / 'launch-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
log = history / 'launch.log'
with log.open('w') as out:
    proc = subprocess.run(['ssh', *ssh_options, HOST, shlex.join(argv)], stdout=out, stderr=subprocess.STDOUT)
receipt['launcher_exit_status'] = proc.returncode
(history / 'launch-result.json').write_text(json.dumps(receipt, indent=2) + '\n')
evidence = TASK / 'build-evidence' / ('v2-' + launch_revision[:12] + '-' + timestamp)
evidence.mkdir(parents=True, exist_ok=False)
subprocess.run(['scp', '-r', *ssh_options, HOST + ':' + str(AUDIT) + '/.', str(evidence)], check=True)
print(json.dumps({'exit_status': proc.returncode, 'launch_revision': launch_revision, 'runner_sha256': runner_sha, 'history': str(history), 'evidence_dir': str(evidence)}, indent=2))
raise SystemExit(proc.returncode)
