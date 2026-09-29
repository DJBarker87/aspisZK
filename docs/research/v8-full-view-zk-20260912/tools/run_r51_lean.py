#!/usr/bin/env python3
"""Focused R51 compile; reuse the source-aware R50 runner without changing it."""
from pathlib import Path

# Run the same cache invalidation and exact target workflow, with only the
# workspace label and base revision changed. The imported runner is source-pinned.
source = Path(__file__).with_name('run_r50_lean.py').read_text()
source = source.replace('r50_focused', 'r51_focused').replace(
    '559e73c6648f42241e998c4e9f3221082da1594a',
    'e5d3c322dd27c3c90b5b486a4ceea9db74564d2e')
exec(compile(source, str(Path(__file__).with_name('run_r50_lean.py')), 'exec'))
