from pathlib import Path
import hashlib, io, json, tarfile

b = Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-20261016')
sha = lambda data: hashlib.sha256(data).hexdigest()
files = {}
changed = [
    'crates/aspis-statement/src/atomic_statement.rs',
    'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',
    'crates/aspis-statement/src/pool_v1/pair_terminal.rs',
    'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs',
    'crates/aspis-statement/src/pool_v1/payment_relation.rs',
    'crates/aspis-statement/examples/j1_terminal_decoder_trace.rs',
]
for sub in ['owned', 'literal', 'slice', 'range']:
    w = b / sub
    pins = json.loads((w / 'input/source-pins.json').read_text())
    for rel, digest in pins['kit_files'].items():
        assert sha((w / 'input' / rel).read_bytes()) == digest, (sub, rel)
    for rel in ['run-host.py', 'input/source-pins.json', 'native-artifact.json',
                'differential.json', *['input/' + p for p in changed]]:
        p = w / rel
        if p.is_file():
            files[str(p.relative_to(b))] = p.read_bytes()
    for folder in ['runs', 'extraction-a']:
        for p in sorted((w / folder).rglob('*')):
            if p.is_file():
                assert p.suffix in ['.py', '.json', '.log', '.llbc', '.lean'], p
                files[str(p.relative_to(b))] = p.read_bytes()
files['j1-rename-enum-constructors.py'] = (b / 'j1-rename-enum-constructors.py').read_bytes()
files['collect-translation.py'] = Path(__file__).read_bytes()
tools = Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
tool_paths = [tools / 'bin/aeneas', tools / 'charon-target/release/charon',
              tools / 'charon-target/release/charon-driver']
files['tool-artifacts.json'] = (json.dumps({str(p): sha(p.read_bytes()) for p in tool_paths}, indent=2) + '\n').encode()
manifest = {n: {'bytes': len(d), 'sha256': sha(d)} for n, d in files.items()}
files['archive-members.json'] = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
dest = b / 'decoder-translation-evidence.tar.gz'
assert not dest.exists()
with tarfile.open(dest, 'w:gz') as tf:
    for name, data in sorted(files.items()):
        info = tarfile.TarInfo(name); info.size = len(data); info.mode = 0o644
        tf.addfile(info, io.BytesIO(data))
print(json.dumps({'archive': str(dest), 'sha256': sha(dest.read_bytes()),
                  'bytes': dest.stat().st_size, 'members': len(files)}, sort_keys=True))
