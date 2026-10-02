"""Focused capped native Rust job. Does not transform the real LLBC."""
import hashlib, json, pathlib, re, shlex, subprocess, sys, time

base = pathlib.Path(__file__).resolve().parent
root = base.parent.parent
action = sys.argv[1]
assert action in ('compile-test', 'compile-main', 'test')
host = 'dombarker@100.108.41.90'
opts = ['-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', '-o',
        'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']
runid = 'aspis-r419-' + action + '-' + str(time.time_ns())
out = base / 'runs' / runid
out.mkdir(parents=True, exist_ok=False)
remote = '/home/dombarker/project-offloads/aspis-r419-native-20261002-a/' + runid
facts = json.loads((base.parent / 'r418-binder-substitution-preflight/remote-workspace/rustc-cache-report.json').read_text())
externs = {a['crate']: a for a in facts['cached_artifacts']}
receipt = {'action': action, 'source_revision': subprocess.check_output(
    ['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
    'resources': {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': 0, 'TasksMax': 128},
    'expected_work': 'focused optimized compilation and linking of downstream native-AST tool; no dependency rebuild' if action.startswith('compile') else 'small native-AST fixtures only',
    'classification': 'UNVERIFIED downstream AST tooling; no source execution or security theorem',
    'toolchain': facts['toolchain'], 'cached_artifacts': facts['cached_artifacts'],
    'runner_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    'source_sha256': {}, 'remote_working_directory': remote,
    'measurement_boundary': 'GNU time child peak RSS and swaps; systemd scope peak is supplementary'}

subprocess.run(['ssh', *opts, host, 'mkdir -p ' + shlex.quote(remote)], check=True)
if action.startswith('compile'):
    for source in sorted((base / 'native').glob('*.rs')):
        data = source.read_bytes()
        (out / source.name).write_bytes(data)
        receipt['source_sha256'][source.name] = hashlib.sha256(data).hexdigest()
        subprocess.run(['scp', *opts, str(out / source.name), host + ':' + remote + '/' + source.name], check=True)
    command = [facts['toolchain']['rustc_path'], '--edition=2024', '-C', 'opt-level=3',
               '-C', 'debuginfo=0', '-C', 'codegen-units=1', '-L',
               'dependency=' + str(pathlib.PurePosixPath(externs['charon_lib']['path']).parent)]
    for name in ['charon_lib', 'derive_generic_visitor', 'index_vec']:
        command.extend(['--extern', name + '=' + externs[name]['path']])
    if action == 'compile-test': command.append('--test')
    command += ['main.rs', '-o', 'native-tests' if action == 'compile-test' else 'normalize']
else:
    previous = pathlib.Path(sys.argv[2])
    prev = json.loads(previous.read_text())
    assert prev['action'] == 'compile-test' and prev['exit_status'] == 0
    assert prev['source_revision'] == receipt['source_revision']
    receipt['compiler_receipt'] = str(previous)
    receipt['compiler_receipt_sha256'] = hashlib.sha256(previous.read_bytes()).hexdigest()
    receipt['source_sha256'] = prev['source_sha256']
    command = [prev['remote_working_directory'] + '/native-tests', '--nocapture', '--test-threads=1']

receipt['command'] = command
receipt_path = out / 'receipt.json'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
script = '''import hashlib,json,pathlib,subprocess,sys
facts=json.loads(sys.argv[1]); sources=json.loads(sys.argv[2]); command=json.loads(sys.argv[3])
for a in facts:
 assert hashlib.sha256(pathlib.Path(a['path']).read_bytes()).hexdigest()==a['sha256'],a['path']
for name,digest in sources.items():
 assert hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()==digest,name
raise SystemExit(subprocess.call(['/usr/bin/time','-v',*command]))
'''
source_checks = receipt['source_sha256'] if action.startswith('compile') else {}
capped = ['systemd-run', '--user', '--wait', '--collect', '--pipe', '--unit=' + runid,
          '--working-directory=' + remote, '-p', 'MemoryHigh=5G', '-p', 'MemoryMax=7G',
          '-p', 'MemorySwapMax=0', '-p', 'TasksMax=128', 'python3', '-c', script,
          json.dumps(facts['cached_artifacts']), json.dumps(source_checks), json.dumps(command)]
with (out / 'raw.log').open('w') as log:
    result = subprocess.run(['ssh', *opts, host, shlex.join(capped)], stdout=log, stderr=subprocess.STDOUT)
raw = (out / 'raw.log').read_text()
receipt['exit_status'] = result.returncode
for key, pat in [('wall_time', r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),
                 ('peak_rss_kib', r'Maximum resident set size \(kbytes\): (\d+)'),
                 ('swaps', r'Swaps: (\d+)')]:
    found = re.search(pat, raw)
    if found: receipt[key] = found[1] if key == 'wall_time' else int(found[1])
receipt['print_axioms'] = 'Not applicable: Rust compiler/tool fixtures, no Lean theorem.'
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(raw)
print('RECEIPT', receipt_path)
raise SystemExit(result.returncode)
