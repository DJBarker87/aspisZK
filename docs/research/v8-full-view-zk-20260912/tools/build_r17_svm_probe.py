#!/usr/bin/env python3
"""Build only the local R17 simulator driver in a bounded host scope."""
import os
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
out = root / 'r17-svm-probe'
assert not out.exists(), 'fresh driver directory required'
(out / 'src').mkdir(parents=True)
original = root / 'docs/research/v8-no-work-100-20260907/experiments/performance-svm'
for name in ('Cargo.toml', 'Cargo.lock'):
    text = (original / name).read_text()
    assert text.count('name = "aspis-v8-performance-svm"') == 1
    (out / name).write_text(text.replace('name = "aspis-v8-performance-svm"',
                                        'name = "aspis-r17-svm-probe"'))
(out / 'src/main.rs').write_bytes(Path(__file__).with_name('r17_svm_probe.rs').read_bytes())
env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', NO_DNA='1',
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-svm/target')
for name in ('RUSTFLAGS', 'RUSTC'):
    env.pop(name, None)
raise SystemExit(subprocess.run(['/usr/bin/time', '-v', '/home/dombarker/.cargo/bin/cargo',
    'build', '--offline', '--locked', '--release', '--jobs', '2', '--manifest-path',
    str(out / 'Cargo.toml')], env=env, cwd=out).returncode)
