from pathlib import Path
import hashlib, io, json, tarfile

b = Path('/home/dombarker/project-offloads/aspis-r1-aeneas-geometry-20261016')
old = Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
decoder = Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-20261016/range')
sha = lambda data: hashlib.sha256(data).hexdigest()
files = {}
for rel in ['geometry.patch', 'source-change.json', 'build-aeneas.sh',
            'run-aeneas-container.py', 'inputs/source-archives.json',
            'aeneas/src/Translate.ml', 'bin/aeneas']:
    files[rel] = (b / rel).read_bytes()
for p in sorted((b / 'aeneas-build-a').rglob('*')):
    if p.is_file(): files[str(p.relative_to(b))] = p.read_bytes()
for rel in ['inputs/aeneas-exact-source.tar.gz', 'inputs/aeneas-source-pins.json',
            'inputs/charon-source-pins.json', 'tools-final-pins.json',
            'aeneas/src/Translate.ml']:
    files['original/' + rel] = (old / rel).read_bytes()
for rel in ['extraction-a/generated-geometry', 'runs/aeneas-geometry-a']:
    for p in sorted((decoder / rel).rglob('*')):
        if p.is_file(): files['decoder/' + str(p.relative_to(decoder))] = p.read_bytes()
changes = json.loads(files['source-change.json'])
for rel, pins in changes['files'].items():
    assert sha((old / rel).read_bytes()) == pins['before'], rel
    assert sha((b / rel).read_bytes()) == pins['after'], rel
files['collect-geometry.py'] = Path(__file__).read_bytes()
files['archive-members.json'] = (json.dumps({n: {'bytes': len(d), 'sha256': sha(d)} for n, d in files.items()}, indent=2, sort_keys=True) + '\n').encode()
dest = b / 'geometry-evidence.tar.gz'; assert not dest.exists()
with tarfile.open(dest, 'w:gz') as tf:
    for name, data in sorted(files.items()):
        info = tarfile.TarInfo(name); info.size = len(data); info.mode = 0o644
        tf.addfile(info, io.BytesIO(data))
print(json.dumps({'archive': str(dest), 'sha256': sha(dest.read_bytes()), 'bytes': dest.stat().st_size, 'members': len(files)}))
