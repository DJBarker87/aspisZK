from pathlib import Path
import sys
r=Path(sys.argv[1]);assert '/pr1-' in str(r)
p=r/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';s=p.read_text();assert 'PR1_TIME' not in s
s=s.replace('    let mut tm = R1CheckTimes::default();','    let pr1_clock=Instant::now();\n    let mut tm = R1CheckTimes::default();')
s=s.replace('    (matches!(verdict, Ok(Some(true))), tm)','    eprintln!("PR1_TIME {} {} {} {} {}",tm.public_data,tm.emit,tm.builders,tm.check,pr1_clock.elapsed().as_secs_f64());\n    (matches!(verdict, Ok(Some(true))), tm)');p.write_text(s)
