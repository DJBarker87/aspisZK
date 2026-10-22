#!/usr/bin/env python3
"""Supplemental missing-evidence pass: semantic transcript and emitter subphases."""
from pathlib import Path
import re,sys
R=Path(sys.argv[1]);p=R/'crates/aspis-r1-cost-probe/src/r1_wire.rs';s=p.read_text()
for fn in ['new','semantic','challenge_reference_circle_point']:
 m=re.search(r'\bfn '+fn+r'\b',s);at=s.index('{',m.end())+1;s=s[:at]+'\nlet _speed_guard=crate::speed_prof::span("semantic_transcript");\n'+s[at:]
p.write_text(s)
p=R/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';s=p.read_text();a='let (cert, _) = emit(&p);';# replace last instance only (p_r1_check)
at=s.rindex(a);s=s[:at]+s[at:].replace(a,'let (cert, info) = emit(&p);\n        eprintln!("SPEED_EMIT_SPLIT {} {} {}", info.t_lifts,info.t_qprime,info.t_bcond);',1);p.write_text(s)
