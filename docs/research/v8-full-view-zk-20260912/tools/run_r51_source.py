#!/usr/bin/env python3
"""Reuse the pinned R42 release runner for a NEW source-first-hit control target."""
from pathlib import Path
source = Path(__file__).with_name('run_r42_root_support.py').read_text()
source = source.replace('r42-', 'r51-').replace(
    "(195 if a.target=='root-support'else 196)", '197').replace(
    '10751450ff23b5c2316b8e220f95a65f6b875ea5',
    'e5d3c322dd27c3c90b5b486a4ceea9db74564d2e')
exec(compile(source, str(Path(__file__).with_name('run_r42_root_support.py')), 'exec'))
