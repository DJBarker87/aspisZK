#!/usr/bin/env python3
"""Aspis extraction probe: export the Cargo closure of one commit from Git as a tar.gz.
The closure rule is the one in PW8_stage.py export() (branch fix/pin2-lean-20261110): every workspace member,
every path dependency reached from them, and every file named by include!/include_str!/include_bytes!.
Reads Git only. usage: XP_export.py <commit> <out.tar.gz> <manifest.json>   (run from the repository)"""
from pathlib import PurePosixPath
import fnmatch, hashlib, io, json, posixpath, re, subprocess, sys, tarfile, tomllib
REV, OUT, MAN = sys.argv[1:4]
def git(*a): return subprocess.check_output(['git', *a])
REV = git('rev-parse', REV).decode().strip()
def safe(p):
    assert p and not p.startswith('/') and '..' not in PurePosixPath(p).parts, p
    return p
def dependency_paths(v):
    if not isinstance(v, dict): return
    for table, entries in v.items():
        if table in ('dependencies', 'dev-dependencies', 'build-dependencies', 'replace'):
            for dep in entries.values():
                if isinstance(dep, dict) and isinstance(dep.get('path'), str): yield dep['path']
        elif table == 'patch':
            for registry in entries.values():
                for dep in registry.values():
                    if isinstance(dep, dict) and isinstance(dep.get('path'), str): yield dep['path']
        elif isinstance(entries, dict): yield from dependency_paths(entries)
tree = {}
for row in git('ls-tree', '-rz', REV).split(b'\0'):
    if not row: continue
    meta, path = row.split(b'\t'); mode, kind, oid = meta.decode().split()
    if kind == 'blob': tree[path.decode()] = (mode, oid)
def blob(p): return git('cat-file', 'blob', tree[safe(p)][1])
root = tomllib.loads(blob('Cargo.toml').decode())
manifests = {p for p in tree if p.endswith('/Cargo.toml')}
roots = set()
for pattern in root['workspace']['members']:
    matched = {str(PurePosixPath(p).parent) for p in manifests if fnmatch.fnmatchcase(str(PurePosixPath(p).parent), pattern)}
    assert matched, ('missing workspace member', pattern)
    roots.update(matched)
members = sorted(roots); queue = list(roots)
for rel in dependency_paths(root):
    p = safe(posixpath.normpath(rel))
    if p not in roots: roots.add(p); queue.append(p)
while queue:
    d = queue.pop(); m = tomllib.loads(blob(d + '/Cargo.toml').decode())
    for rel in dependency_paths(m):
        p = safe(posixpath.normpath(posixpath.join(d, rel)))
        assert p + '/Cargo.toml' in tree, ('missing path manifest', d, rel)
        if p not in roots: roots.add(p); queue.append(p)
selected = {'Cargo.toml', 'Cargo.lock'}
selected.update(p for p in tree if any(p.startswith(d + '/') for d in roots))
queue = list(selected)
while queue:
    p = queue.pop()
    if not p.endswith('.rs'): continue
    text = blob(p).decode(errors='replace')
    for rel in re.findall(r'include(?:_str|_bytes)?!\s*\(\s*"([^"]+)"', text):
        q = posixpath.normpath(posixpath.join(posixpath.dirname(p), rel))
        if q.startswith('..') or q not in tree: continue   # include outside the tree or generated at build time
        if q not in selected: selected.add(q); queue.append(q)
pins = {}; total = 0
with tarfile.open(OUT, 'w:gz') as tar:
    for p in sorted(selected):
        raw = blob(p); mode, oid = tree[p]
        info = tarfile.TarInfo(p); info.size = len(raw); info.mode = int(mode, 8) & 0o777; info.mtime = 0
        tar.addfile(info, io.BytesIO(raw))
        pins[p] = dict(sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw), git_blob=oid)
        total += len(raw)
json.dump(dict(revision=REV, workspace_members=members, package_roots=sorted(roots), files=pins), open(MAN, 'w'), indent=1, sort_keys=True)
print(json.dumps(dict(revision=REV, packages=len(roots), files=len(pins), bytes=total, tar_sha256=hashlib.sha256(open(OUT, 'rb').read()).hexdigest())))
