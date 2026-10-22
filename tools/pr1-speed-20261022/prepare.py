#!/usr/bin/env python3
"""Measurement-only changes in task-owned host snapshots."""
from pathlib import Path
import sys
r=Path(sys.argv[1]);assert str(r).startswith('/home/dombarker/project-offloads/codex-cx-ct-kernels-v2-20261022/pr1-')
p=r/'crates/aspis-r1-cost-probe/examples/ct_fixture_gate.rs';s=p.read_text()
s=s.replace('let mut records = Vec::new();','let mut records = Vec::new();\n    for run in 0..3 {')
s=s.replace('"{}-{name}",','"{}-{name}-{run}",')
s=s.replace('    #[cfg(feature = "private-leaf-salts")]\n    {','    }\n    #[cfg(feature = "private-leaf-salts")]\n    {',1)
s=s.replace('"fixture_count": records.len(),','"fixture_count": records.len(),')
p.write_text(s)
p=r/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';s=p.read_text();s=s.replace('    (matches!(verdict, Ok(Some(true))), tm)','    eprintln!("PR1_TIME {} {} {} {}",tm.public_data,tm.emit,tm.builders,tm.check);\n    (matches!(verdict, Ok(Some(true))), tm)');p.write_text(s)

p=r/'crates/aspis-r1-cost-probe/examples/pr1_challenges.rs';p.write_bytes((r/'tools/pr1-speed-20261022/challenges.rs').read_bytes())
