#!/usr/bin/env python3
"""Verify the exact SBF source owner and its bounded body comparison."""
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
meta=(ROOT/'toolchain/sbf-metadata.txt').read_text()
assert 'rustc 1.89.0-dev' in meta and 'commit-hash: unknown' in meta and 'commit-date: unknown' in meta
assert 'LLVM version: 20.1.7' in meta
assert 'd95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002' in meta
version=(ROOT/'toolchain/platform-tools-version.md').read_text().splitlines()
assert version[0]=='790f1537507dbdb0da320fbb3b1c1eca3b33c474  https://github.com/anza-xyz/rust.git'
fetch=json.loads((ROOT/'upstream-fetch.json').read_text())
assert len(fetch['checks'])==2
for x in fetch['checks']:
    assert x['http_status']==200 and x['matches_installed_sbf_rust_src'] is True
    assert sha(ROOT/'source/sbf/core/array/mod.rs' if x['path'].endswith('array/mod.rs') else ROOT/'source/sbf/core/ops/try_trait.rs')==x['sha256']
for p in ROOT.rglob('*'):
    if p.is_file():
        assert p.suffix.lower() not in {'.o','.a','.so','.rlib','.bin','.elf'}
        assert 'keypair' not in p.name.lower()
