"""Read-only provenance assessment and job-owned source copy; no build/extraction."""
from pathlib import Path
import hashlib, json, shutil, subprocess

T = Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain')
S = T/'aeneas-full'
D = Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
D.mkdir(exist_ok=True)
assert not (D/'base').exists(), 'Never overwrite a pinned candidate'

def pin(p):
    b = p.read_bytes()
    return dict(sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))

revision = subprocess.check_output(['git', '-C', str(S), 'rev-parse', 'HEAD'], text=True).strip()
assert revision == 'b59d5188c082f704a418c7cb4e52ad69328002d1'
patch = subprocess.check_output(['git', '-C', str(S), 'diff', '--binary', '--full-index', 'HEAD'])
(D/'accepted-extensions.patch').write_bytes(patch)
(D/'historical-extensions.patch').write_bytes((T/'aeneas-b59d5188-lean432.patch').read_bytes())
# Preserve post-archive differences explicitly, including Lean-only fixes.
delta = subprocess.run(['diff', '-u', str(D/'historical-extensions.patch'), str(D/'accepted-extensions.patch')], capture_output=True).stdout
(D/'extension-archive-difference.diff').write_bytes(delta)
files = subprocess.check_output(['git', '-C', str(S), 'ls-files', '-z']).decode().split('\0')
manifest, cached = {}, []
for rel in filter(None, files):
    p = S/rel
    if not p.is_file():
        continue
    dst = D/'base'/rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(p, dst, follow_symlinks=False)
    if p.is_symlink():
        manifest[rel] = dict(symlink=str(p.readlink()))
    else:
        manifest[rel] = pin(p)
    if rel.startswith('src/') and p.suffix in ['.ml', '.mli']:
        built = S/'src/_build/default'/rel.removeprefix('src/')
        cached.append(dict(path=rel, live=pin(p), cached=pin(built) if built.is_file() else None))

# Charon's OCaml source was retained beside the original backend; copy only
# source/configuration, never its artifacts, and pin every dependency file.
charon = T/'charon-full'
deps = {}
for p in sorted(charon.rglob('*')):
    rel = p.relative_to(charon)
    if any(x in rel.parts for x in ['_build', 'target', '.git']) or not p.is_file():
        continue
    dst = D/'charon'/rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(p, dst, follow_symlinks=False)
    deps[str(rel)] = dict(symlink=str(p.readlink())) if p.is_symlink() else pin(p)
(D/'base/charon').symlink_to('../charon')
exe = T/'output/aeneas-b59d5188-lean432-extended-static'
cached_exe = S/'src/_build/default/main.exe'
assert pin(exe) == pin(cached_exe)
assert all(x['live'] == x['cached'] for x in cached), 'Cached source mismatch'
result = dict(schema='ProverRwRngExtractor-base-provenance-v1', base_revision=revision,
    source_revision='96f7984a59', source_manifest=manifest, charon_dependency_manifest=deps,
    accepted_extensions=pin(D/'accepted-extensions.patch'),
    installed_binary=pin(exe), cached_binary=pin(cached_exe), cached_source_comparison=cached,
    assessment='All retained OCaml source copies match cached build inputs; cached executable equals installed binary. Corroborates source association, not a reproducible rebuild. Exact tracked source and all extensions copied into job-owned base; no installed source/binary changed.',
    build_attempts=0, extraction_invocations=0, print_axioms='N/A: read-only provenance and source copy')
(D/'base-provenance.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: result[k] for k in ['base_revision', 'accepted_extensions', 'installed_binary', 'assessment']}))
