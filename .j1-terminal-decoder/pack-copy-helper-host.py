from pathlib import Path
import hashlib, json, tarfile, io, shutil

root = Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-copy-helper-proof-20261016')
extraction = Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-20261016/copy-helper')
shutil.copy2(extraction/'extraction-a/TerminalDecoder.llbc', root/'original/TerminalDecoder.llbc')
for label in ('charon-a','aeneas-a'):
    dest = root/'original'/label
    dest.mkdir(exist_ok=True)
    for p in (extraction/'runs'/label).iterdir():
        if p.is_file(): shutil.copy2(p, dest/p.name)
for path in (
    'crates/aspis-statement/src/atomic_statement.rs',
    'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',
    'crates/aspis-statement/src/pool_v1/payment_relation.rs',
    'crates/aspis-statement/src/pool_v1/pair_terminal.rs',
    'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs',
    'crates/aspis-core/src/field.rs',
):
    dest = root/'original/source'/path
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(extraction/'input'/path,dest)
files = {}
for rel in ('original','proofs/sources','proofs/objects','proofs/successful-targets','proofs/runs'):
    for p in (root/rel).rglob('*'):
        if p.is_file() and not p.is_symlink(): files[str(p.relative_to(root))] = p
files['proofs/runner.py'] = root/'proofs/runner.py'
hashes = {n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in sorted(files.items())}
out = root/'decoder-closed-cone.tar.gz'
with tarfile.open(out,'w:gz') as t:
    seen = {}
    for n,p in sorted(files.items()):
        h = hashes[n]
        if h in seen:
            m=tarfile.TarInfo(n);m.type=tarfile.LNKTYPE;m.linkname=seen[h];t.addfile(m)
        else:
            t.add(p,arcname=n,recursive=False);seen[h]=n
    data=''.join(h+'  '+n+'\n' for n,h in hashes.items()).encode()
    m=tarfile.TarInfo('SHA256SUMS');m.size=len(data);t.addfile(m,io.BytesIO(data))
print(json.dumps({'archive':out.name,'entries':len(files)+1,'bytes':out.stat().st_size,
                 'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))
