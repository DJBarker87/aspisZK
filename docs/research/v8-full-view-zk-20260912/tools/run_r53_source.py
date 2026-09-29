#!/usr/bin/env python3
"""Pinned release replay of Lean-exported fixtures through actual source APIs."""
from pathlib import Path
source=Path(__file__).with_name('run_r42_root_support.py').read_text()
source=source.replace('r42-','r53-').replace("(195 if a.target=='root-support'else 196)",'197')
source=source.replace('a=p.parse_args()',"p.add_argument('--fixture',type=Path,required=True);a=p.parse_args()")
source=source.replace('10751450ff23b5c2316b8e220f95a65f6b875ea5','a26a468746e9551769ce1d17104050e1fc1bf1fc')
source=source.replace('run([str(binary)],a.target)','run([str(binary),str(a.fixture)],a.target)')
source=source.replace("'overflow_checks':True","'fixture_sha256':sha(a.fixture),'overflow_checks':True")
exec(compile(source,str(Path(__file__).with_name('run_r42_root_support.py')),'exec'))
