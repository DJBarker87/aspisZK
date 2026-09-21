#!/usr/bin/env python3
"""Focused optimized adapter gate; invoke inside a zero-swap build scope."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(sys.argv[1]).resolve()
stage = json.loads((root / 'r17-stage.json').read_text())
env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', NO_DNA='1',
    RUSTFLAGS=stage['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
# The whole historical host binary's test configuration imports unrelated prover
# unit tests requiring HOST_HASH. Compile only the actual changed modules.
out = Path(tempfile.mkdtemp(prefix='adapter-gate-', dir=root))
exp = root / 'docs/research/v8-no-work-100-20260907/experiments'
source = out / 'gate.rs'
source.write_text(f'''#![allow(dead_code, unexpected_cfgs)]
#[path="{root / 'crates/aspis-core/src/field.rs'}"] pub mod field;
pub mod corelib {{ pub use crate::field; }}
#[path="{exp / 'r17_structured_g.rs'}"] mod r17_structured_g;
#[path="{exp / 'r17_mask_workspace.rs'}"] mod r17_mask_workspace;
fn main() {{
    for case in 0..16usize {{
        let point = core::array::from_fn(|i| field::QM31::from_cm31(
            field::CM31::from_m31(field::M31((1 + case * 11 + i) as u32))));
        assert_eq!(r17_structured_g::mask_weights(&point),
            r17_structured_g::mask_weights_reference(&point));
    }}
    println!("PASS: 16 actual adapter/reference comparisons, all 1024 entries");
}}
''')
subprocess.run(['/usr/bin/time', '-v', '/home/dombarker/.cargo/bin/rustc',
    '--edition=2021', '-O', str(source), '-o', str(out / 'gate')], env=env, check=True)
raise SystemExit(subprocess.run(['/usr/bin/time', '-v', str(out / 'gate')], env=env).returncode)
