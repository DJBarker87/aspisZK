#!/usr/bin/env python3
"""Checked extraction of the actual QM31 try-inverse closure.
Expected work is dependency-free release Rust compilation and translation.
Run only in a bounded, swap-disabled build-host scope.
"""
from pathlib import Path
here = Path(__file__).parent
source = (here / 'extract_r64_field.py').read_text()
for old, new in [
    ("'r64-field-extraction'", "'r66-field-extraction'"),
    ('crate::inverse_probe', 'crate::quartic_inverse_probe'),
    ('R64Field', 'R66Field'),
]:
    assert old in source
    source = source.replace(old, new)
exec(compile(source, str(here / 'extract_r64_field.py'), 'exec'))
