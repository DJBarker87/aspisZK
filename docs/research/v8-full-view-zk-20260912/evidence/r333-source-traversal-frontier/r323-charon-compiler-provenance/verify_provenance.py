#!/usr/bin/env python3
from pathlib import Path
import hashlib
import subprocess

root = Path(__file__).resolve().parent
expected = {
    'pinned-charon/toolchain.rs': 'c1eb50a7ecdfc4d816f70c474617400d88dfb4bf0eee5ab7f2b7177f27b001c6',
    'pinned-charon/main.rs': '381774440aec829cb23ad9849102673f2085366910537a4ff56177133df6b35f',
    'pinned-charon/driver.rs': '41e7a384d484fc31603578086d273a61f15ea0d3ba76ff534805435a47aafa84',
    'pinned-charon/Cargo.toml': 'a31bab7d34638f8c2a43f14263184a3328ab17366c2f9acf201d86b922c4176f',
    'pinned-charon/Cargo.lock': 'c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67',
    'pinned-charon/rust-toolchain': '27e050e8fc5ac827e1264abf38c27fcaf18e73f4305104c866179cb84721898c',
    'nightly-rust-source/iterator.rs': 'db43b7acc33fca53d85fef3ddea29ec9f8c1e768df428676fe2de160f21d5f6b',
    'nightly-rust-source/iterator-r322-copy.rs': 'db43b7acc33fca53d85fef3ddea29ec9f8c1e768df428676fe2de160f21d5f6b',
    'stable-rust-source/iterator-r322-fetched-stable.rs': 'd1e767ee2018c20100362f56e35dbcb1efa592a31e972ccba0a469c9b5832589',
}
for name, want in expected.items():
    got = hashlib.sha256((root / name).read_bytes()).hexdigest()
    if got != want:
        raise SystemExit(f'{name}: expected {want}, got {got}')
# Ensure R322's downloaded nightly source and the direct installed-toolchain copy are identical.
assert (root/'nightly-rust-source/iterator.rs').read_bytes() == (root/'nightly-rust-source/iterator-r322-copy.rs').read_bytes()
# Report exact source landmarks from copied source.
source = (root/'nightly-rust-source/iterator.rs').read_text().splitlines()
assert source[2485].strip().startswith('fn try_fold<')
assert '[const] Destruct' in source[2488]
checks = subprocess.run(['shasum', '-a', '256', '-c', 'SHA256SUMS'], cwd=root, text=True, capture_output=True)
if checks.returncode:
    raise SystemExit(checks.stdout + checks.stderr)
print(checks.stdout, end='')
print('Selected nightly try_fold signature/bounds at 2486/2489 verified.')
