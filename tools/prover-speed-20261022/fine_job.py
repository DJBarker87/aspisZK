#!/usr/bin/env python3
"""Reuse identical runner with distinct names for one supplemental pair."""
from pathlib import Path
import sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-speed-20261022');mode,stage=sys.argv[1:]
s=(H/'tools/host_job.py').read_text()
s=s.replace("O=H/'receipts'/(mode+'-'+stage)","O=H/'receipts'/(mode+'-fine-'+stage)")
s=s.replace("str(H/'bin'/mode),'5',str(H/('results-'+mode))", "str(H/'bin'/(mode+'-fine')),'1',str(H/('results-'+mode+'-fine'))")
s=s.replace("q=H/'bin'/mode;", "q=H/'bin'/(mode+'-fine');")
s=s.replace('ten proof generations (5 each fixture)', 'two supplemental proof generations (1 each fixture)')
s=s.replace("['research','v2']","['research-fine','v2-fine']")
exec(compile(s,'host_job_fine','exec'))
