#!/usr/bin/env python3
"""Repair a missing parent-timer artifact in the task-owned measurement copy."""
from pathlib import Path
import sys
r=Path(sys.argv[1]);assert '/pr1-' in str(r)
p=r/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';s=p.read_text()
a='    let mut tm = R1CheckTimes::default();';assert s.count(a)==1
s=s.replace(a,'    let pr1_clock = Instant::now();\n'+a)
a='    eprintln!("PR1_TIME {} {} {} {}",tm.public_data,tm.emit,tm.builders,tm.check);';assert s.count(a)==1
s=s.replace(a,'    eprintln!("PR1_TIME {} {} {} {} {}",tm.public_data,tm.emit,tm.builders,tm.check,pr1_clock.elapsed().as_secs_f64());');p.write_text(s)

p=r/'crates/aspis-r1-cost-probe/examples/ct_fixture_gate.rs';s=p.read_text().replace('args.len() == 2,','(args.len() == 2 || args.len() == 3),').replace('for run in 0..3 {', 'for run in 0..args.get(2).map(|v| v.parse::<usize>().unwrap()).unwrap_or(3) {');p.write_text(s)
