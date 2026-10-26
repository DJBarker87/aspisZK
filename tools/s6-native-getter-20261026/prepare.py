#!/usr/bin/env python3
"""Reconstruct a native getter harness with safe scalar constructors."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

R = Path(__file__).resolve().parents[2]
REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
O = Path(sys.argv[1]).resolve()
O.mkdir()  # No existing workspace may be replaced.
sha = lambda b: hashlib.sha256(b).hexdigest()
def git(*args):
    return subprocess.check_output(['git', *args], cwd=R)
prefixes = ['crates/aspis-core', 'crates/aspis-statement', 'tools/r1-builder-reference'] + [
    'docs/research/v8-r0-zk-20261009/refine/' + n for n in ['writers', 'blockwriters', 'poseidon']]
originals = {}
for prefix in prefixes:
    for p in git('ls-tree', '-r', '--name-only', REV, prefix).decode().splitlines():
        if not (p.endswith('.rs') or p.endswith('/Cargo.toml')):
            continue
        b = git('show', REV + ':' + p)
        target = O / p
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(b)
        originals[p] = sha(b)
# Resolve literal Rust path/include dependencies before compiling; this also
# covers cfg(kani) reference modules which production-only inventories omit.
import os
import re
while True:
    added = 0
    for relative in list(originals):
        if not relative.endswith('.rs'):
            continue
        text = (O / relative).read_text()
        paths = re.findall(r'#[\[]path\s*=\s*"([^"]+)"[\]]', text)
        paths += re.findall(r'include(?:_str|_bytes)?!\(\s*"([^"]+)"', text)
        for literal in paths:
            target = os.path.normpath(str(Path(relative).parent / literal))
            assert not target.startswith('../') and not Path(target).is_absolute()
            if target in originals:
                continue
            value = git('show', REV + ':' + target)
            destination = O / target
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(value)
            originals[target] = sha(value)
            added += 1
    if not added:
        break

# Only dev/test dependency declarations are omitted from the isolated native
# fixture. All production features and normal dependencies are retained.
manifest_changes = {}
for crate in ['aspis-core', 'aspis-statement']:
    p = 'crates/' + crate + '/Cargo.toml'
    before = (O / p).read_text()
    after = before.split('[dev-dependencies]')[0]
    (O / p).write_text(after)
    manifest_changes[p] = {'before_sha256': sha(before.encode()), 'after_sha256': sha(after.encode()),
                           'omitted_suffix': before[len(after):]}
# No production type/body attributes are needed: explicit independent scalar
# constructors below avoid generic array::from_fn loops in the harness.
selected = {}
attribute = ''
(O / 'Cargo.toml').write_text('''[workspace]
resolver = "2"
members = ["harness", "crates/aspis-core", "crates/aspis-statement", "docs/research/v8-r0-zk-20261009/refine/writers", "docs/research/v8-r0-zk-20261009/refine/blockwriters", "docs/research/v8-r0-zk-20261009/refine/poseidon"]
[workspace.package]
edition = "2021"
license = "MIT OR Apache-2.0"
version = "0.1.0"
[workspace.dependencies]
aspis-core = { path = "crates/aspis-core" }
''')
(O / 'harness/src').mkdir(parents=True)
(O / 'harness/Cargo.toml').write_text('''[package]
name = "s6-native-getter"
version = "0.0.0"
edition = "2021"
[dependencies]
aspis-statement = { path = "../crates/aspis-statement", features = ["r0"] }
aspis-core = { path = "../crates/aspis-core", features = ["r0"] }
''')
(O / 'harness/src/lib.rs').write_bytes((Path(__file__).parent / 'proofs.rs').read_bytes())
files = {str(p.relative_to(O)): sha(p.read_bytes()) for p in sorted(O.rglob('*')) if p.is_file()}
binding = {'schema': 'focused-extractor-proof-packet-v1', 'release_revision': REV,
           'original_source_pins': originals, 'files': files,
           'proof_only_arbitrary_derives': selected, 'derive_attribute': attribute,
           'construction': 'explicit independent scalar calls in literal arrays; complete typed fields, both enum variants',
           'manifest_changes': manifest_changes,
           'qualification': 'All native getter bodies/types unchanged. Explicit scalar constructors '
                            'initialize typed values safely and impose no semantic/canonicality premise. '
                            'Kani default allocation model; no decoder/SDK/runtime/release closure.'}
(O / 'binding.json').write_text(json.dumps(binding, indent=2) + '\n')
print(json.dumps({'workspace': str(O), 'files': len(files), 'proof_only_derives': 0}))
