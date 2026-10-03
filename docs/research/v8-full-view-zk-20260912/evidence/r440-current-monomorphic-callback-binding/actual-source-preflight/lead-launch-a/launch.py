#!/usr/bin/env python3
"""Prepared R440 actual-source capture launcher; remains closed until explicit lead authorization."""
import hashlib, io, json, os, pathlib, shlex, subprocess, sys, tarfile

H = pathlib.Path(__file__).resolve().parent
W = next(p for p in H.parents if (p / '.git').exists())
HOST = 'dombarker@100.108.41.90'
SSH_OPTS = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']
REMOTE_ROOT = '/home/dombarker/project-offloads/aspis-r440-actual-mono-closure-20261003-a'
REMOTE_WORKDIR = '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE_SCRIPT = H / 'remote.py'
LAUNCH_REVISION = '3b9e8d7f0122e6dc966a809904adbd722ae3079d'
OWN_UNIT = 'aspis-r440-actual-mono-closure.service'

if os.environ.get('R440_ACTUAL_SOURCE_CAPTURE_ALLOW') != '1':
    raise SystemExit('capture gate closed; require lead review and R440_ACTUAL_SOURCE_CAPTURE_ALLOW=1')
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=W, text=True).strip()
assert revision == LAUNCH_REVISION, (revision, LAUNCH_REVISION)
assert not (H / 'launch-status.json').exists() and not (H / 'saved-output').exists()
script_sha = hashlib.sha256(REMOTE_SCRIPT.read_bytes()).hexdigest()
if len(sys.argv) != 2 or sys.argv[1] != script_sha:
    raise SystemExit(f'pass reviewed remote.py SHA256 as sole argument: {script_sha}')
probe = subprocess.run(['ssh', *SSH_OPTS, HOST, 'test ! -e ' + shlex.quote(REMOTE_ROOT)])
assert probe.returncode == 0, 'remote output root exists or SSH access failed; nothing launched/collected'
cmd = [
    'systemd-run', '--user', '--wait', '--collect', '--pipe', f'--unit={OWN_UNIT}',
    f'--working-directory={REMOTE_WORKDIR}',
    '-p', 'MemoryHigh=5G', '-p', 'MemoryMax=7G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=128',
    '-p', 'KillMode=control-group', '-p', 'TimeoutStopSec=10s', '-p', 'RuntimeMaxSec=600s',
    '--setenv=R440_ACTUAL_SOURCE_CAPTURE_ALLOW=1', 'python3', '-c', REMOTE_SCRIPT.read_text()
]
argv = ['ssh', *SSH_OPTS, HOST, shlex.join(cmd)]
(H / 'ssh-argv.json').write_text(json.dumps({'argv': argv, 'remote_script_sha256': script_sha, 'launch_revision': revision}, indent=2))
with (H / 'ssh-launch.log').open('wb') as f:
    run = subprocess.run(argv, stdout=f, stderr=subprocess.STDOUT)
(H / 'launch-status.json').write_text(json.dumps({'ssh_exit_status': run.returncode, 'remote_script_sha256': script_sha, 'launch_revision': revision}, indent=2))
collect = subprocess.run(['ssh', *SSH_OPTS, HOST, shlex.join(['tar', '-czf', '-', '-C', REMOTE_ROOT, '.']),], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
(H / 'collection.stderr.log').write_bytes(collect.stderr)
(H / 'collection-status.json').write_text(json.dumps({'exit_status': collect.returncode, 'tar_bytes': len(collect.stdout), 'sha256': hashlib.sha256(collect.stdout).hexdigest()}, indent=2))
if collect.returncode == 0:
    (H / 'saved-output').mkdir()
    with tarfile.open(fileobj=io.BytesIO(collect.stdout), mode='r:gz') as archive:
        for member in archive.getmembers():
            path = pathlib.PurePosixPath(member.name)
            assert not path.is_absolute() and '..' not in path.parts and (member.isfile() or member.isdir()), member.name
        archive.extractall(H / 'saved-output', filter='data')
print('CAPTURE_EXIT', run.returncode, 'COLLECTION_EXIT', collect.returncode)
sys.exit(run.returncode or collect.returncode)
